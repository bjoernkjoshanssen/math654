import tactic
noncomputable theory

/-
Design your own short register machine program and either
(i) prove that it halts,
(ii) prove that it doesn't halt, or
(iii) prove that ψₚ is finitely satisfiable [this is equivalent to (i) actually, but more work]
following the examples indicated below.

You should indicate what the register machine program is;
you don't need to include the "informal proof" of whether it halts or not.
-/

namespace does_halt

constant A : Type
constant O : A → A → Prop
constant c : A
constant f : A → A
constant R : A → A → A → Prop
-- R s L m says that at after s stages completed,
-- we are at line L with m in register R₀

def bar0 : A := f c
def bar1 : A := f bar0
def bar2 : A := f bar1
def bar3 : A := f bar2
def bar4 : A := f bar3

local infix `<` := O
def ψ₀ : Prop :=
  (∀ x y z, x < y → y < z → x < z) ∧
  (∀ x, ¬ x < x) ∧
  (∀ x y, x < y ∨ x = y ∨ y < x) ∧
  (∀ x, c < x ∨ c = x) ∧
  (∀ x, x < f x ∨ x = f x) ∧
  (∀ x, (∃ y, x < y) → x < f x ∧
  ∀ z, x < z → f x < z ∨ f x = z)
  /-
  Program that halts:
  0 if R₀=◫ then 2 else 1
  1 if R₀=◫ then 1 else 1 (goto 1)
  2 R₀ = R₀ + |
  3 print
  4 halt
  Uses only one register so n=0.
  -/

  def ψα₀ : Prop :=
    ∀ x y₀, (R x bar0 y₀ → x < f x ∧ ((y₀ = bar0 ∧ R (f x) bar2 y₀)
    ∨ (¬ y₀ = bar0 ∧ R (f x) bar1 y₀)))

  def ψα₁ : Prop := 
    ∀ x y₀, R x bar1 y₀ → x < f x ∧ (y₀ = bar0 ∧ R (f x) bar1 y₀)
    ∨ (¬ y₀ = bar0 ∧ R (f x) bar1 y₀)

  def ψα₂ : Prop := ∀ x y₀, R x bar2 y₀ → x < f x ∧ R (f x) bar3 (f y₀)
  def ψα₃ : Prop := ∀ x y₀, R x bar3 y₀ → x < f x ∧ R (f x) bar4 y₀

  def ψₚ := ψ₀ ∧ (R bar0 bar0 bar0) ∧ ψα₀ ∧ ψα₁ ∧ ψα₂ ∧ ψα₃

  def φₚ := ψₚ → ∃ x, ∃ y₀, R x bar4 y₀

  theorem this_program_does_halt :  φₚ :=
  λ hψₚ, 
    have h0: R bar0 bar0 bar0, from hψₚ.2.1,
    have hψα₀ : ψα₀,           from hψₚ.2.2.1,
    have hψα₁ : ψα₁,           from hψₚ.2.2.2.1,
    have hψα₂ : ψα₂,           from hψₚ.2.2.2.2.1,
    have hψα₃ : ψα₃,           from hψₚ.2.2.2.2.2,
    have h1: R bar1 bar2 bar0, from (hψα₀ bar0 bar0 h0).2.elim (λ h0, h0.2) (λ h0, false.elim (h0.1 (eq.refl _))),
    have h2: R bar2 bar3 bar1, from (hψα₂ bar1 bar0 h1).2,
    have h3: R bar3 bar4 bar1, from (hψα₃ bar2 bar1 h2).2,
    exists.intro bar3 (exists.intro bar1 (h3))

  /- Informal proof:
  Assume ψₚ. In particular R bar0 bar0 bar0
  (we start with empty register at line 0 at time 0).
  Then we apply ψα₀ with x=bar0 and y=bar0,
  to get R bar1 bar2 bar0.
  Then we apply ψα₂ to get R bar2 bar3 bar1.
  Then we apply ψα₃ to get R bar3 bar4 bar1.
  Then we use exists.intro to finish.
  -/

theorem finitely_satisfiable :
  ∃ A : Type, ∃ T: fintype A,
  ∃ O : A → A → Prop,
  ∃ c : A,
  ∃ f : A → A,
  ∃ R : A → A → A → Prop,
  ψₚ := exists.intro (fin 5) (
    exists.intro (fin.fintype 5) (
      exists.intro (
        λ x y, nat.lt x.1 y.1
      ) (
        exists.intro 0 (
          exists.intro (λ x, ite (x=4) (nat.succ x.1) 4) (
            exists.intro (
              λ x y z, ((x.1,y.1,z.1)=(0,0,0)) -- h0
              ∨ (x.1,y.1,z.1)=(1,2,0)
              ∨ (x.1,y.1,z.1)=(2,3,1)
              ∨ (x.1,y.1,z.1)=(3,4,1)
              -- spell out the computation using h0 h1 h2 h3: 000 120 231 341
            ) (
              and.intro (and.intro (
                λ x y z hxy hyz,
                
                -- have x.1 < y.1, from hxy,
                sorry --nat.lt_trans hxy hyz -- show < on fin 5 is transitive
              ) (
                sorry
              )
              ) (
                and.intro sorry (
                  and.intro sorry (
                    and.intro sorry (
                      and.intro sorry sorry
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

end does_halt

namespace does_not_halt

def A := ℕ
def O := (λ x y, nat.lt x y)
def c : ℕ := 0
def f := nat.succ
def bar0 := c
def bar1 := f c
def R : ℕ → ℕ → ℕ → Prop := (λ s L r:ℕ, L=bar0 ∧ r=bar0)

local infix `<` := O
def ψ₀ : Prop :=
  (∀ x y z, x < y → y < z → x < z) ∧
  (∀ x, ¬ x < x) ∧
  (∀ x y, x < y ∨ x = y ∨ y < x) ∧
  (∀ x, c < x ∨ c = x) ∧
  (∀ x, x < f x ∨ x = f x) ∧
  (∀ x, (∃ y, x < y) → x < f x ∧
  ∀ z, x < z → f x < z ∨ f x = z)

  /-
  Program that does not halt:
  0 if R₀=◫ then 0 else 0
  1 halt
  Uses only one register so n=0.
  -/

def PQ : Prop := ∃! x : ℕ, x =x

  def ψα₀ : Prop :=
    ∀ x y₀, (R x bar0 y₀ → x < f x ∧ ((y₀ = bar0 ∧ R (f x) bar0 y₀)
    ∨ (¬ y₀ = bar0 ∧ R (f x) bar0 y₀)))

  def ψₚ := ψ₀ ∧ (R bar0 bar0 bar0) ∧ ψα₀

  def φₚ := ψₚ → ∃ x, ∃ y₀, R x bar1 y₀

  theorem this_program_does_not_halt : ¬ φₚ :=

          λ hφₚ,
          have hψₚ: ψₚ, from and.intro (
            show (∀ x y z, x < y → y < z → x < z) ∧
            (∀ x, ¬ x < x) ∧
            (∀ x y, x < y ∨ x = y ∨ y < x) ∧
            (∀ x, c < x ∨ c = x) ∧
            (∀ x, x < f x ∨ x = f x) ∧
            (∀ x, (∃ y, x < y) → x < f x ∧
            ∀ z, x < z → f x < z ∨ f x = z)
          , from 
            and.intro (λ x y z, nat.lt_trans) (
              and.intro (
                λ h, (lt_self_iff_false h).mp
              ) (
                and.intro (
                  λ x y : ℕ, show nat.lt x y ∨ x = y ∨ nat.lt y x, from trichotomous x y
                ) (
                  and.intro (
                    λ x,
                    lt_or_eq_of_le (zero_le x)
                  ) (
                    and.intro (
                      λ x, or.inl (nat.lt_succ_self x)
                    ) (
                      λ x hx, and.intro (nat.lt_succ_self x) (
                        λ z hz, lt_or_eq_of_le (nat.succ_le_of_lt hz)
                      )
                    )
                  )
                )
              )
            )
          ) (
            and.intro (
              and.intro rfl rfl
            ) (
              λ x y₀, λ hR, and.intro (
                nat.lt_succ_self _
              ) (
                or.inl (
                  and.intro hR.2 (and.intro rfl hR.2)
                )
              )
            )
          ),

          have ∃ x, ∃ y₀, R x bar1 y₀, from hφₚ hψₚ,
          exists.elim this (
            λ x hx,
            exists.elim hx (
              λ y₀ hy₀,
              have hR1: R bar0 bar1 y₀, from hy₀,
              have bar1 = bar0 ∧ y₀ = bar0, from by {rw R at hR1,exact hR1,},
              have bar0 = bar1, from this.1.symm,
              nat.zero_ne_one this
            )
          )
end does_not_halt
