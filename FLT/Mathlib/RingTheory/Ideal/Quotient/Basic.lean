/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard, Adam McKenna
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Regular.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

namespace Ideal.Quotient

section ProdEquivSpanMul

variable {R : Type*} [CommRing R] {α β : R}

namespace Internal

/-- Forward map of `Ideal.Quotient.prodEquivSpanMul`: a section of the quotient
`R → R ⧸ (α * β)` built from representatives in `R ⧸ (α)` and `R ⧸ (β)`,
sending `(i, j)` to `i.out + α * j.out` modulo `α * β`. -/
noncomputable def prodSpanMulFun (α β : R) :
    (R ⧸ Ideal.span ({α} : Set R)) × (R ⧸ Ideal.span ({β} : Set R)) →
      R ⧸ Ideal.span ({α * β} : Set R) :=
  fun p => Ideal.Quotient.mk (Ideal.span ({α * β} : Set R)) (p.1.out + α * p.2.out)

lemma prodSpanMulFun_apply (α β : R)
    (p : (R ⧸ Ideal.span ({α} : Set R)) × (R ⧸ Ideal.span ({β} : Set R))) :
    prodSpanMulFun α β p =
      Ideal.Quotient.mk (Ideal.span ({α * β} : Set R)) (p.1.out + α * p.2.out) :=
  rfl

lemma prodSpanMulFun_injective (hα : IsLeftRegular α) :
    Function.Injective (prodSpanMulFun α β) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  rw [prodSpanMulFun_apply, prodSpanMulFun_apply, Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at h
  -- Step 1: `α ∣ i₁.out - i₂.out`, since `α ∣ α * β ∣ …` modulo `α ∣ α * (j₁.out - j₂.out)`.
  have hαβ : α * β ∣ (i₁.out - i₂.out) + α * (j₁.out - j₂.out) := by
    have hrew : i₁.out + α * j₁.out - (i₂.out + α * j₂.out) =
        (i₁.out - i₂.out) + α * (j₁.out - j₂.out) := by ring
    rwa [hrew] at h
  have hα_dvd : α ∣ i₁.out - i₂.out :=
    (dvd_add_left ⟨_, rfl⟩).mp (dvd_trans ⟨β, rfl⟩ hαβ)
  have hi : i₁ = i₂ := by
    rw [← Ideal.Quotient.mk_out i₁, ← Ideal.Quotient.mk_out i₂, Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact hα_dvd
  -- Step 2: Substitute `i₁ = i₂`, leaving `α * β ∣ α * (j₁.out - j₂.out)`; cancel `α`.
  subst hi
  have hαβ_dvd_α : α * β ∣ α * (j₁.out - j₂.out) := by
    have hrew : i₁.out + α * j₁.out - (i₁.out + α * j₂.out) = α * (j₁.out - j₂.out) := by ring
    rw [hrew] at h; exact h
  have hβ_dvd : β ∣ j₁.out - j₂.out := by
    obtain ⟨c, hc⟩ := hαβ_dvd_α
    refine ⟨c, hα ?_⟩
    change α * (j₁.out - j₂.out) = α * (β * c)
    rw [hc]; ring
  have hj : j₁ = j₂ := by
    rw [← Ideal.Quotient.mk_out j₁, ← Ideal.Quotient.mk_out j₂, Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact hβ_dvd
  exact Prod.ext rfl hj

lemma prodSpanMulFun_surjective :
    Function.Surjective (prodSpanMulFun (α := α) (β := β)) := by
  intro k
  set i : R ⧸ Ideal.span ({α} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({α} : Set R)) k.out
  obtain ⟨m, hm⟩ : α ∣ k.out - i.out := by
    rw [← Ideal.mem_span_singleton]
    have hs := Ideal.Quotient.out_sub (Ideal.span ({α} : Set R)) k.out
    have hrew : k.out - i.out = -(i.out - k.out) := by ring
    rw [hrew]; exact neg_mem hs
  set j : R ⧸ Ideal.span ({β} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({β} : Set R)) m
  refine ⟨(i, j), ?_⟩
  rw [prodSpanMulFun_apply, ← Ideal.Quotient.mk_out k, Ideal.Quotient.eq,
    Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ : β ∣ j.out - m := by
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.out_sub _ m
  -- Combine `j.out = m + β * c` and `k.out = i.out + α * m`.
  refine ⟨c, ?_⟩
  change i.out + α * j.out - k.out = α * β * c
  have hjout : j.out = m + β * c := by rw [← hc]; ring
  have hkout : k.out = i.out + α * m := by rw [← hm]; ring
  rw [hjout, hkout]; ring

end Internal

/-- For a commutative ring `R` and a left-regular `α : R`, there is a bijection
`(R ⧸ (α)) × (R ⧸ (β)) ≃ R ⧸ (α * β)` sending `(i, j)` to `i.out + α * j.out`. -/
noncomputable def prodEquivSpanMul (hα : IsLeftRegular α) (β : R) :
    (R ⧸ Ideal.span ({α} : Set R)) × (R ⧸ Ideal.span ({β} : Set R)) ≃
      R ⧸ Ideal.span ({α * β} : Set R) :=
  Equiv.ofBijective (Internal.prodSpanMulFun α β)
    ⟨Internal.prodSpanMulFun_injective hα, Internal.prodSpanMulFun_surjective⟩

@[simp]
lemma prodEquivSpanMul_apply (hα : IsLeftRegular α) (β : R)
    (p : (R ⧸ Ideal.span ({α} : Set R)) × (R ⧸ Ideal.span ({β} : Set R))) :
    prodEquivSpanMul hα β p =
      Ideal.Quotient.mk (Ideal.span ({α * β} : Set R)) (p.1.out + α * p.2.out) :=
  rfl

end ProdEquivSpanMul

end Ideal.Quotient
