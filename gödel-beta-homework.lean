import tactic
import algebra.group.defs
import data.vector
import data.nat.basic
import data.nat.nth

noncomputable theory

def starStar  (u q j a : ℕ) (b₁ b₂ : fin u.succ) (b₀ : fin b₁.1): Prop :=
-- property the b's should have
    u = b₀.1 + b₁.1 * ((j+1) + a*q + b₂.1 * q*q)
    ∧
    (∃ c: fin b₁.1.succ, b₁.1 = c.1*c.1)
    ∧
    ∀ d: fin b₁.1, d.1 ≠ 1 → d.1 ∣ (b₁.1) →  q ∣ d.1

def βexist (u q j a : ℕ) : Prop := a < q ∧ ∃ b₁ b₂ : fin u.succ, ∃ b₀ : fin b₁.1, starStar u q j a b₁ b₂ b₀

def φβ (u q j a : ℕ) : Prop :=
  (βexist u q j a ∧ ∀ aa: fin a, ¬ βexist u q j aa.1) ∨
  ((∀ aa:fin q, ¬ βexist u q j aa.1) ∧ a = 0)

def stage₁ (s p t z y₀ : ℕ) : Prop := 
φβ t p (2*s) z ∧ φβ t p (2*s+1) y₀

-- Example program 0 R₀ += ∣, 1 HALT
def inc_R0_once (u:fin 1) (u':fin 2) (u₀ u₀' : ℕ) : Prop :=
  -- in general it should depend on u but here u must be 0
  u'.1 = u.1 + 1 ∧ u₀' = u₀ + 1

-- Example program 0 R₀ += ∣, 1 R₀ -= ∣, 2 HALT 
def inc_dec_R0 (u:fin 2) (u':fin 3) (u₀ u₀' : ℕ) : Prop :=
  (u.1=0 → u'.1 = u.1 + 1 ∧ u₀' = u₀ + 1)
  ∧
  (u.1=1 → u'.1 = u.1 + 1 ∧ u₀' = u₀ - 1) -- monus
 
 -- Homework program: 0 R₀ += ∣, 1 PRINT, 2 HALT
def inc_R0_print (u:fin 2) (u':fin 3) (u₀ u₀' : ℕ) : Prop :=
  (u.1=0 → u'.1 = u.1 + 1 ∧ u₀' = u₀ + 1)
  ∧
  (u.1=1 → u'.1 = u.1 + 1 ∧ u₀' = u₀)


def χ_steps (k:ℕ)(program:(fin k)→(fin k.succ)→ℕ→ ℕ→Prop) (t p i:ℕ) : Prop :=
  ∀ u:fin k, ∀ u₀:ℕ, ∀ u':fin k.succ, ∀ u₀' : ℕ, 
  stage₁ i p t u u₀ → stage₁ (i+1) p t u' u₀' →
  program u u' u₀ u₀' 


 def χ₁ (k:ℕ) (program:(fin k)→(fin k.succ)→ℕ→ℕ→Prop) (x₀ z y₀ : ℕ) : Prop := ∃ s p t : ℕ,
  stage₁ 0 p t 0 x₀ ∧
  stage₁ s p t z y₀ ∧
  ∀ i:fin s,  χ_steps k program t p i.1


 /-

  χ₁ Program:
    0 R₀ = R₀ + ∣,
    1 HALT
  t p should encode the sequence 0,0, 1,0 (line number 0, R₀=0, line number 1, R₀=0)

  χ₁' Program:
    0 R₀ = R₀ + ∣,
    1 IF R₀ = □ THEN 1 ELSE 2,
    2 HALT
 -/


def b_0 (i p:ℕ) (a_ : vector (fin p) i) : ℕ :=
  (list.of_fn (λ j:fin i, j.1.succ * (p ^ (2*j.1)))).sum
    +
  (list.of_fn (λ j:fin i, (a_.nth j).1 * p ^ (2*j.1+1))).sum

def t {r:ℕ} (p:ℕ) (a_ : vector (fin p) r.succ) : ℕ :=
b_0 r.succ p a_

def b_1 (i p:ℕ) : ℕ := p^(2*i)

theorem easy {j i r : ℕ} (h: j < r.succ - (i+1)): i+1+j<r.succ:= lt_tsub_iff_left.mp h

def b_2  (i p :ℕ){r:ℕ} (a_ : vector (fin p) (r.succ)) : ℕ :=
  (list.of_fn (λ j:fin (r.succ-(i+1)), (a_.nth (⟨i+1+j.1,easy j.2⟩)).1 * p ^ (2*j.1+1))).sum
  +
  (list.of_fn (λ j:fin (r-i), (i+2+j.1) * p ^ (2*j.1))).sum

def vector_take {n:ℕ} {α:Type}
   (x : vector α n) (i:ℕ) (h: i≤ n) : vector α i :=
  ⟨(x.take i).1, eq.trans ((x.take i).2) (min_eq_left h)⟩

#eval (nat.prime 11 : bool)

example : nat.prime 11 := sorry -- to avoid having to prove this, we state "decode" and "encode" in a simplified way:

theorem decode {p r:ℕ}   (a_ : vector (fin p) r.succ)(i:fin r.succ): -- (hprime: nat.prime p):
φβ (t p a_) p i (a_.nth i)
:= sorry

theorem encode {p:ℕ}  ( r i:ℕ)(h:i<r.succ)
(a_ : vector (fin p) r.succ) (a:ℕ):
φβ (t p a_) p i a → a = (a_.nth i)
:= λ hφβ, sorry

theorem le_succ_succ {i j:ℕ}: i < j.succ.succ → i ≤ j ∨ i=j.succ :=
λ h, nat.of_le_succ (nat.lt_succ_iff.mp h)

theorem lt_one {i:ℕ} : i < 1 → i=0 := nat.lt_one_iff.mp

theorem lt_two {i:ℕ} : i < 2 → i=0∨ i=1
  :=
  λ h2,
    have i ≤ 0 ∨ i = 1, from le_succ_succ h2,
    this.elim
      (λ h, or.inl (nat.le_zero_iff.mp h))
      (λ h1, or.inr ( h1))

theorem lt_three {i:ℕ} : i < 3 → i=0∨ i=1∨ i=2
  :=
  λ h3,
  have i ≤ 2, from nat.lt_succ_iff.mp h3,
  (em (i=2)).elim (
    λ h2, or.inr (or.inr h2)
  ) (
    λ hn2,
    have i<2,           from ne.lt_of_le hn2 this,
    have i ≤ 0 ∨ i = 1, from le_succ_succ this,

    this.elim
      (λ h, or.inl (nat.le_zero_iff.mp h))
      (λ h1, or.inr (or.inl h1))
  )

theorem true_of_eq {P:ℕ → Prop} {i j :ℕ} (he: i=j) (hP: P j): P i := cast (congr_arg P he).symm hP

theorem of_lt_3 {P:ℕ → Prop}: P 0 → P 1 → P 2 → ∀ i:fin 3, P i.1 :=
λ h0 h1 h2 i, (lt_three i.2).elim (
     λ h, true_of_eq h h0
  ) (
    λ h12, h12.elim
    (λ h, true_of_eq h h1)
    (λ h, true_of_eq h h2)
  )

theorem of_lt_2 {P:ℕ → Prop}: P 0 → P 1 → ∀ i:fin 2, P i.1 :=
λ h0 h1 i, (lt_two i.2).elim (
     λ h, true_of_eq h h0
  ) (
    λ h, true_of_eq h h1
  )

theorem of_lt_1 {P:ℕ → Prop}: P 0 → ∀ i:fin 1, P i.1 :=
  λ h0 i, true_of_eq (lt_one i.2) h0

theorem does_halt_longer: χ₁ 2 inc_dec_R0 0 2 0 :=
  let p := 11 in
  let a_ := (⟨[0,0,1,1,2,0],rfl⟩: vector (fin p) 6) in
  let r := 5 in
  exists.intro 2 ( -- number of steps s=2
    exists.intro p (
      exists.intro (t p a_) (
        and.intro (
          and.intro (decode a_ 0) (decode a_ 1)
        ) (
          and.intro (
            and.intro (decode a_ 4) (decode a_ 5)
          ) (
            of_lt_2 (
              λ u u₀ u' u₀' h0 h1,
              let t:= t p a_, hu := h0.1, hu₀ := h0.2, hu' := h1.1, hu₀' := h1.2 in
              and.intro (
                λ hu0,
                and.intro (
                  calc u'.1 = 1: encode r 2 dec_trivial a_ u'.1 hu'
                        ... = 0+1: by ring
                        ... = u.1+1: by rw hu0
                ) (
                    have Hu₀: u₀ = (vector.nth a_ 1).1, from encode r 1 dec_trivial a_ u₀ hu₀,
                    show  u₀' = u₀ + 1, from calc
                            _ = (vector.nth a_ 3).1: encode r 3 dec_trivial a_ u₀' hu₀'
                          ... = 0+1: by ring
                          ... = (vector.nth a_ 1).1 + 1: rfl
                          ... = u₀+1: by rw Hu₀
                )
              ) (
                λ hu1, -- show line number 1 at stage 0 doesn't, and can't, happen
                false.elim (
                  have u.1 = 0, from encode r 0 dec_trivial a_ u hu,
                  zero_ne_one (eq.trans this.symm hu1)
                )
              )
            ) (
            let t:= t p a_ in
            show   ∀ u:fin 2, ∀ u₀:ℕ, ∀ u':fin 3, ∀ u₀' : ℕ, 
            stage₁ 1 p t u u₀ → stage₁ (1+1) p t u' u₀' →
            inc_dec_R0 u u' u₀ u₀', from
            λ u u₀ u' u₀' h0 h1,
            let hu := h0.1, hu₀ := h0.2, hu' := h1.1, hu₀' := h1.2 in
            show   (u.1=0 → u'.1 = u.1 + 1 ∧ u₀' = u₀ + 1)
                  ∧
                  (u.1=1 → u'.1 = u.1 + 1 ∧ u₀' = u₀ - 1) -- monus
                , from
            and.intro (
              λ hu0,-- can't happen
              false.elim (
                have u.1 = 1, from encode r 2 dec_trivial a_ u hu,
                zero_ne_one (eq.trans hu0.symm this)
              )
            ) (
              λ hu1,
              and.intro (
                calc u'.1 = 2: encode r 4 dec_trivial a_ u'.1 hu'
                      ... = 1+1: by ring
                      ... = u.1+1: by rw hu1
              ) (
                  have Hu₀: u₀ = (vector.nth a_ 3).1, from encode r 3 dec_trivial a_ u₀ hu₀,
                  show  u₀' = u₀ - 1, from calc
                          _ = (vector.nth a_ 5).1: encode r 5 dec_trivial a_ u₀' hu₀'
                        ... = 1-1: by ring
                        ... = (vector.nth a_ 3).1 - 1: rfl
                        ... = u₀-1: by rw Hu₀
                )
              )
            )
          )
        )
      )
    )
  )

 theorem does_halt: χ₁ 1 inc_R0_once 0 1 1 :=
  let p := 5 in
  let a_ := (⟨[0,0,1,1],rfl⟩: vector (fin p) 4) in
  let r := 3 in -- r is length a_ minus one
  exists.intro 1 (
    exists.intro p
    (
      exists.intro (t p a_)
      (
        and.intro (
          and.intro (decode a_ 0) (decode a_ 1)
        ) (
          and.intro (
            and.intro (decode a_ 2) (decode a_ 3)
          ) (
            of_lt_1 (
              λ u u₀ u' u₀',
              λ hfst hsnd,
              let hu := hfst.1, hu₀ := hfst.2, hu' := hsnd.1, hu₀' := hsnd.2 in
              and.intro (
              calc u'.1 = 1: encode r 2 dec_trivial a_ u'.1 hu'
                  ... = 0+1: by ring
                  ... = u.1+1: by rw (lt_one u.2)
              ) (
              have Hu₀: u₀ = (vector.nth a_ 1).1, from encode r 1 dec_trivial a_ u₀ hu₀,
              show  u₀' = u₀ + 1, from calc
                      _ = (vector.nth a_ r).1: encode r r dec_trivial a_ u₀' hu₀'
                    ... = 0+1: by ring
                    ... = (vector.nth a_ 1).1 + 1: rfl
                    ... = u₀+1: by rw Hu₀
              )
            )
          )
        )
      )
    )
  )

theorem homework: χ₁ 2 inc_R0_print 0 2 1 := -- starting at config (0,0), we get to config (2,1)
-- HOMEWORK
sorry
