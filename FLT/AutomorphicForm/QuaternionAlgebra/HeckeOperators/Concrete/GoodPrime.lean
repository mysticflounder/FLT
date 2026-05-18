/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper, Adam McKenna
-/
module

public import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Local -- abstract Hecke ops
public import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Abstract -- abstract Hecke ops
public import FLT.AutomorphicForm.QuaternionAlgebra.Defs -- definitions of automorphic forms
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits -- for (π 0; 0 1)
public import FLT.Mathlib.RingTheory.Ideal.Quotient.Basic
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import FLT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Concrete Hecke operators, good-prime setup

Common scaffolding (level subgroup `U₁(S)`, finiteness lemma) plus the `T_v` Hecke
operator at a good prime `v ∉ S`, together with the double-coset decomposition for
`T_v` formalised in the `GoodPrime` namespace.
-/

@[expose] public section
/-

# Concrete Hecke operators

Hecke operators for spaces of automorphic forms on totally definite quaternion algebras
of level `U₁(S)`, where `S` is a finite set of finite places of the totally real number
field `F`, and `U₁(S)` is the matrices which are of the form `(a *;0 a)` mod `v` for
all `v ∈ S`.

## Main definitions

All in the `TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm` namespace.

Let `r : Rigidification F D` be an `𝔸_F^∞`-algebra isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`,
needed to interpret the local factors `Dᵥ` as matrix rings so we can define Hecke operators
as matrices.

* `HeckeOperator.T r R v` -- the Hecke operator `Tᵥ` associated to `(ϖᵥ 0; 0 1)` at a (good)
  place `v` (via the rigidification `r`), as an `R`-linear endomorphism of
  `WeightTwoAutomorphicFormOfLevel (U1 r S) R`.

-/

/-

## A finiteness result

The existence of abstract Hecke operators relies on a certain double coset space being
a finite union of single cosets. In our situation we can supply this finiteness proof
via a topological argument, which we abstract here.

-/

section finiteness

open Topology Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {g : G} {U V : Subgroup G}

open scoped Pointwise in
lemma QuotientGroup.mk_image_finite_of_compact_of_open
    (hU : IsCompact (U : Set G)) (hVopen : IsOpen (V : Set G)) :
    (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)).Finite := by
  have : DiscreteTopology (G ⧸ V) := by
    rw [discreteTopology_iff_forall_isOpen]
    intro s
    rw [← (isQuotientMap_mk V).isOpen_preimage, ← (QuotientGroup.mk_surjective).image_preimage s,
      preimage_image_mk_eq_iUnion_image, iUnion_subtype]
    conv in ⋃ x ∈ _, _ => change ⋃ x ∈ (V : Set G), _
    rw [iUnion_mul_right_image]
    exact IsOpen.mul_left hVopen
  exact ((hU.mul <| isCompact_singleton).image continuous_mk).finite_of_discrete

end finiteness


open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain

-- let F be a totally real number field
variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

-- Let D/F be a quaternion algebra
variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

-- Let r be a rigidification of D, which is a collection of isomorphisms D ⊗ Fᵥ = M₂(Fᵥ)
-- for all finite places v of F, compatible with the adelic structure (i.e. inducing
-- an isomorphism D ⊗_F 𝔸_F^f = M₂(𝔸_F^f))
variable (r : Rigidification F D)

-- Let S be a finite set of finite plaes of F (the level)
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- let P be a good prime
variable {P : HeightOneSpectrum (𝓞 F)} (hP : P ∉ S)

open TotallyDefiniteQuaternionAlgebra
-- let's define T_P : S_2^D(U_1(S)) -> S_2^D(U_1(S))
namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

open IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing.GL2.Internal

open scoped TensorProduct

-- Oops! This is also `IsDedekindDomain.HeightOneSpectrum.QuaternionAlgebra.TameLevel`
-- in `FLT.QuaternionAlgebra.NumberField`, defined differently (using `Subgroup.comap` not `map`).
-- Don't care which one survives.
variable {F D} in
open scoped TensorProduct.RightActions in
/-- U1(S) -/
noncomputable abbrev U1 : Subgroup (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ :=
  Subgroup.map (Units.map r.symm.toMonoidHom) (GL2.TameLevel S)

namespace Internal

variable {F D} in
open scoped TensorProduct.RightActions in
omit [IsTotallyReal F] in
lemma U1_compact :
    IsCompact (U1 r S : Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) := by
  rw [U1, Subgroup.coe_map]
  have hc : Continuous r.symm :=
    IsDedekindDomain.HeightOneSpectrum.Rigidification.continuous_invFun D r
  exact (GL2.TameLevel.isCompact S).image
    (Continuous.units_map r.symm.toMonoidHom hc)

variable {F D} in
open scoped TensorProduct.RightActions in
omit [IsTotallyReal F] in
lemma U1_open :
    IsOpen (U1 r S : Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) := by
  rw [U1, Subgroup.coe_map]
  have hcr : Continuous r :=
    IsDedekindDomain.HeightOneSpectrum.Rigidification.continuous_toFun D r
  rw [Set.image_eq_preimage_of_inverse
    (f := Units.map r.symm.toMonoidHom)
    (g := Units.map r.toMonoidHom)
    (fun x => by ext; simp) (fun x => by ext; simp)]
  exact (GL2.TameLevel.isOpen S).preimage
    (Continuous.units_map r.toMonoidHom hcr)

end Internal

variable (R : Type*) [CommRing R]

namespace HeckeOperator

variable {F D S} in
open scoped TensorProduct.RightActions in
/-- The Hecke operator T_v as an R-linear map from R-valued quaternionic weight 2
automorphic forms of level U_1(S).
-/
noncomputable def T (v : HeightOneSpectrum (𝓞 F)) :
    WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
    WeightTwoAutomorphicFormOfLevel (U1 r S) R :=
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  let g : (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ :=
    Units.mapEquiv r.symm.toMulEquiv
      (FiniteAdeleRing.GL2.restrictedProduct.symm
        (RestrictedProduct.mulSingle _ v
          (Local.GL2.diag (Local.uniformizerInt (F := F) v)
            (Local.Internal.uniformizerInt_ne_zero (F := F) v))))
  AbstractHeckeOperator.HeckeOperator (R := R) g (U1 r S) (U1 r S)
  (QuotientGroup.mk_image_finite_of_compact_of_open
    (Internal.U1_compact r S) (Internal.U1_open r S))

section T

variable {F D}

open scoped TensorProduct.RightActions
open scoped Pointwise

noncomputable instance : DecidableEq (HeightOneSpectrum (𝓞 F)) :=
  Classical.typeDecidableEq _

namespace GoodPrime

/-- The chosen local uniformizer in the integer ring of the completion. -/
noncomputable abbrev uniformizerInt (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletionIntegers F :=
  Local.uniformizerInt (F := F) v

omit [IsTotallyReal F] in
lemma uniformizerInt_ne_zero (v : HeightOneSpectrum (𝓞 F)) :
    uniformizerInt (F := F) v ≠ 0 :=
  Local.Internal.uniformizerInt_ne_zero (F := F) v

/-- The representative for the `swap * diag` good-prime coset. -/
noncomputable def swap_mul_diag (v : HeightOneSpectrum (𝓞 F)) :
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Units.mapEquiv r.symm.toMulEquiv
    (FiniteAdeleRing.GL2.restrictedProduct.symm
      (RestrictedProduct.mulSingle _ _
        ((Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1) *
          Local.GL2.diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v))))

/-- The representative for the unipotent good-prime coset. -/
noncomputable def unipotent_mul_diag (v : HeightOneSpectrum (𝓞 F))
    (α : v.adicCompletionIntegers F) (hα : α ≠ 0)
    (t : ↑(adicCompletionIntegers F v) ⧸ Ideal.span {α}) :
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Units.mapEquiv r.symm.toMulEquiv
    (FiniteAdeleRing.GL2.restrictedProduct.symm
      (RestrictedProduct.mulSingle _ _
        (Local.GL2.unipotent_mul_diag α hα (Quotient.out t : adicCompletionIntegers F v))))

/-- The option-indexed family of good-prime representatives. -/
noncomputable def goodPrimeRep (v : HeightOneSpectrum (𝓞 F)) :
    Option (↑(adicCompletionIntegers F v) ⧸ Ideal.span {uniformizerInt (F := F) v}) →
      (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ
| none => swap_mul_diag (r := r) v
| some t => unipotent_mul_diag (r := r) v (uniformizerInt (F := F) v)
    (uniformizerInt_ne_zero (F := F) v) t

/-- The image of the good-prime representative family. -/
noncomputable def goodPrimeRep_image (v : HeightOneSpectrum (𝓞 F)) :
    Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  (goodPrimeRep (r := r) v) '' ⊤

/-- Blueprint-facing name for the good-prime coset family used in the `T_v` decomposition.
This is the image of the option-indexed representative family above. -/
noncomputable def T_cosets_image (v : HeightOneSpectrum (𝓞 F)) :
    Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  goodPrimeRep_image (r := r) v

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma unipotent_mul_diag_inj (v : HeightOneSpectrum (𝓞 F)) :
    Set.InjOn (unipotent_mul_diag (r := r) v (uniformizerInt (F := F) v)
      (uniformizerInt_ne_zero (F := F) v)) ⊤ := by
  intro t₁ h₁ t₂ h₂ h
  simp only [unipotent_mul_diag, EmbeddingLike.apply_eq_iff_eq, RestrictedProduct.ext_iff] at h
  let h' := h v; simp only [RestrictedProduct.mulSingle_eq_same, Units.ext_iff] at h'
  rw [← Matrix.ext_iff] at h'
  let h'' := h' 0 1
  simpa [Local.GL2.unipotent_mul_diag, Matrix.GeneralLinearGroup.GL2.unipotent, Local.GL2.diag,
    Matrix.unitOfDetInvertible, Matrix.GeneralLinearGroup.diagonal] using h''

-- `simp` here unfolds `swap_mul_diag`/`unipotent_mul_diag` against the swap matrix
-- whose entries differ by branch; the relevant rewrites differ per case split.
set_option linter.flexible false in
omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma goodPrimeRep_inj (v : HeightOneSpectrum (𝓞 F)) :
    Set.InjOn (goodPrimeRep (r := r) v) ⊤ := by
  intro x hx y hy hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some t =>
          exfalso
          have h :
              swap_mul_diag (r := r) v =
                unipotent_mul_diag (r := r) v (uniformizerInt (F := F) v)
                  (uniformizerInt_ne_zero (F := F) v) t := hxy
          simp only [swap_mul_diag, unipotent_mul_diag, EmbeddingLike.apply_eq_iff_eq,
            RestrictedProduct.ext_iff] at h
          have h0 := h v
          simp only [RestrictedProduct.mulSingle_eq_same, Units.ext_iff] at h0
          rw [← Matrix.ext_iff] at h0
          have h00 := h0 0 0
          simp [Local.GL2.unipotent_mul_diag, Matrix.GeneralLinearGroup.GL2.unipotent,
            Local.GL2.diag, Matrix.GeneralLinearGroup.swap, Matrix.swap,
            Matrix.unitOfDetInvertible, Matrix.GeneralLinearGroup.diagonal] at h00
          have h00' : uniformizerInt (F := F) v = 0 := by
            apply Subtype.ext
            simpa [eq_comm] using h00
          exact (uniformizerInt_ne_zero (F := F) v) h00'
  | some t =>
      cases y with
      | none =>
          exfalso
          have h :
              unipotent_mul_diag (r := r) v (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) t =
                swap_mul_diag (r := r) v := by
            simpa [goodPrimeRep] using hxy
          simp only [swap_mul_diag, unipotent_mul_diag, EmbeddingLike.apply_eq_iff_eq,
            RestrictedProduct.ext_iff] at h
          have h0 := h v
          simp only [RestrictedProduct.mulSingle_eq_same, Units.ext_iff] at h0
          rw [← Matrix.ext_iff] at h0
          have h00 := h0 0 0
          simp [Local.GL2.unipotent_mul_diag, Matrix.GeneralLinearGroup.GL2.unipotent,
            Local.GL2.diag, Matrix.GeneralLinearGroup.swap, Matrix.swap,
            Matrix.unitOfDetInvertible, Matrix.GeneralLinearGroup.diagonal] at h00
          have h00' : uniformizerInt (F := F) v = 0 := by
            apply Subtype.ext
            simpa [eq_comm] using h00
          exact (uniformizerInt_ne_zero (F := F) v) h00'
      | some t' =>
          have h' :
              unipotent_mul_diag (r := r) v (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) t =
              unipotent_mul_diag (r := r) v (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) t' := by
            simpa [goodPrimeRep, unipotent_mul_diag] using hxy
          exact congrArg some ((unipotent_mul_diag_inj (r := r) v) trivial trivial h')

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
lemma goodPrimeRep_commute_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hvw : v ≠ w)
    (a : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) (ha : a ∈ goodPrimeRep_image (r := r) v)
    (b : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) (hb : b ∈ goodPrimeRep_image (r := r) w) :
    a * b = b * a := by
  rcases ha with ⟨x, _, rfl⟩
  rcases hb with ⟨y, _, rfl⟩
  cases x <;> cases y <;>
    exact ((RestrictedProduct.mulSingle_commute
        (i := v) (j := w) hvw _ _).map
      (FiniteAdeleRing.GL2.restrictedProduct (F := F)).symm.toMonoidHom |>.map
      (Units.mapEquiv r.symm.toMulEquiv).toMonoidHom).eq

end GoodPrime

end T

end HeckeOperator

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm
