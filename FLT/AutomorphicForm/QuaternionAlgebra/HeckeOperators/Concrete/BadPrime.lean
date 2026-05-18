/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper, Adam McKenna
-/
module

public import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete.GoodPrime

/-!
# Concrete Hecke operators, bad-prime setup

Defines the bad-prime Hecke operator `U_{v,α}` (for `v ∈ S`, `α ∈ 𝓞ᵥ` nonzero) and proves
the double-coset decomposition needed for its action. Also proves the cross-prime
commutation lemmas (`T_v ∘ T_w = T_w ∘ T_v`, `T_v ∘ U_{w,β}` ..., `U_{v,α} ∘ U_{w,β}`...)
inside `namespace Internal`; these feed `HeckeAlgebra.instCommRing` in the next file.
-/

@[expose] public section

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]
variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]
variable (r : Rigidification F D)
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (R : Type*) [CommRing R]

open TotallyDefiniteQuaternionAlgebra

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

open IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing.GL2.Internal

open scoped TensorProduct

namespace HeckeOperator

section U

variable {F D}

variable {v : HeightOneSpectrum (𝓞 F)} (α : v.adicCompletionIntegers F) (hα : α ≠ 0)

open scoped TensorProduct.RightActions
open scoped Pointwise

noncomputable instance : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _

/-- The (global) matrix element `diag[α, 1]`. -/
noncomputable abbrev diag :
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Units.mapEquiv r.symm.toMulEquiv
    (FiniteAdeleRing.GL2.restrictedProduct.symm
    (RestrictedProduct.mulSingle _ _ (Local.GL2.diag α hα)))

/-- The (global) matrix element `(unipotent t) * (diag α hα) = !![α, t; 0, 1]`.
Here `t ∈ 𝒪ᵥ / α` and we lift it arbitrarily to `𝒪ᵥ`. -/
noncomputable def unipotent_mul_diag (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α})) :
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Units.mapEquiv r.symm.toMulEquiv
    (FiniteAdeleRing.GL2.restrictedProduct.symm
    (RestrictedProduct.mulSingle _ _
      (Local.GL2.unipotent_mul_diag α hα (Quotient.out t : adicCompletionIntegers F v))))

/-- The set of elements `unipotent_mul_diag`, that is, the elements of `(D ⊗ 𝔸_F^∞)ˣ`
which are `(α t;0 1)` at `v` and the identity elsewhere, as `t` runs through a set
of coset reps of `𝓞ᵥ / α`. These will form a set of coset representatives for `U1 diag U1`.
-/
noncomputable def unipotent_mul_diag_image :
    Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  (unipotent_mul_diag r α hα) '' ⊤

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
lemma unipotent_mul_diag_inj :
    Set.InjOn (unipotent_mul_diag r α hα) ⊤ := by
  intro t₁ h₁ t₂ h₂ h
  simp only [unipotent_mul_diag, EmbeddingLike.apply_eq_iff_eq, RestrictedProduct.ext_iff] at h
  let h' := h v; simp only [RestrictedProduct.mulSingle_eq_same, Units.ext_iff] at h'
  rw [← Matrix.ext_iff] at h'
  let h'' := h' 0 1
  simpa [Local.GL2.unipotent_mul_diag, Matrix.GeneralLinearGroup.GL2.unipotent, Local.GL2.diag,
    Matrix.unitOfDetInvertible, Matrix.GeneralLinearGroup.diagonal] using h''

/-- The double coset space `U₁(S) diag(αᵥ,1) U₁(S)` as a set of left cosets. -/
noncomputable def doubleCoset :
    Set ((D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ ⧸ (U1 r S)) :=
  QuotientGroup.mk '' ((U1 r S) * {diag r α hα})

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma mapsTo_leftCoset_doubleCoset :
    Set.MapsTo QuotientGroup.mk (unipotent_mul_diag_image r α hα) (doubleCoset r S α hα) := by
  rintro _ ⟨i, _, rfl⟩
  set u_glob : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
    Units.mapEquiv r.symm.toMulEquiv
      (FiniteAdeleRing.GL2.restrictedProduct.symm
        (RestrictedProduct.mulSingle _ v
          (Matrix.GeneralLinearGroup.GL2.unipotent
            ((Quotient.out i : adicCompletionIntegers F v) :
              adicCompletion F v)))) with hu_glob_def
  have hu_glob_mem : u_glob ∈ U1 r S := by
    refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
    refine ⟨fun w => ?_, fun w _ => ?_⟩
    · by_cases hwv : w = v
      · subst hwv
        rw [toAdicCompletion_symm_mulSingle_self w _]
        exact (Local.GL2.unipotent_mem_U1 (v := w) (Quotient.out i)).1
      · rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
        exact (GL2.localFullLevel w).one_mem
    · by_cases hwv : w = v
      · subst hwv
        rw [toAdicCompletion_symm_mulSingle_self w _]
        exact Local.GL2.unipotent_mem_U1 (v := w) (Quotient.out i)
      · rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
        exact (GL2.localTameLevel w).one_mem
  have h_eq : unipotent_mul_diag r α hα i = u_glob * diag r α hα := by
    rw [hu_glob_def]
    unfold unipotent_mul_diag diag
    rw [← map_mul, ← map_mul, ← RestrictedProduct.mulSingle_mul]
    rfl
  refine ⟨u_glob * diag r α hα, Set.mul_mem_mul hu_glob_mem rfl, ?_⟩
  rw [← h_eq]

set_option maxHeartbeats 400000 in
-- The rigidification roundtrip in `h_image` is expensive: a six-step rewrite chain
-- pushing `Units.mapEquiv r.symm` and `mulSingle` inverse/mul through the embedding.
omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma injOn_leftCoset_doubleCoset :
    Set.InjOn (QuotientGroup.mk (s := U1 r S)) (unipotent_mul_diag_image r α hα) := by
  rintro _ ⟨i, _, rfl⟩ _ ⟨j, _, rfl⟩ h
  refine congrArg (unipotent_mul_diag r α hα) ?_
  have hratio : (unipotent_mul_diag r α hα i)⁻¹ * (unipotent_mul_diag r α hα j) ∈ U1 r S :=
    QuotientGroup.eq.mp h
  set t_i : adicCompletionIntegers F v := Quotient.out i
  set t_j : adicCompletionIntegers F v := Quotient.out j
  set g_loc : GL (Fin 2) (adicCompletion F v) :=
    (Local.GL2.unipotent_mul_diag α hα t_i)⁻¹ *
      Local.GL2.unipotent_mul_diag α hα t_j with hg_loc_def
  set w' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    FiniteAdeleRing.GL2.restrictedProduct.symm
      (RestrictedProduct.mulSingle _ v g_loc) with hw'_def
  have h_image : Units.mapEquiv r.symm.toMulEquiv w' =
      (unipotent_mul_diag r α hα i)⁻¹ * (unipotent_mul_diag r α hα j) := by
    change Units.mapEquiv r.symm.toMulEquiv
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v g_loc)) =
      (unipotent_mul_diag r α hα i)⁻¹ * (unipotent_mul_diag r α hα j)
    unfold unipotent_mul_diag
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← RestrictedProduct.mulSingle_inv,
      ← RestrictedProduct.mulSingle_mul]
  obtain ⟨w, hw_mem, hw_eq⟩ := Subgroup.mem_map.mp hratio
  have hw'_eq : w' = w := by
    apply (Units.mapEquiv r.symm.toMulEquiv).injective
    rw [h_image]; exact hw_eq.symm
  have hw'_mem : w' ∈ GL2.TameLevel S := hw'_eq ▸ hw_mem
  have hg_loc_mem : g_loc ∈ GL2.localFullLevel v := by
    have := hw'_mem.1 v
    rwa [hw'_def, toAdicCompletion_symm_mulSingle_self v g_loc] at this
  have h01_int : ((g_loc : GL (Fin 2) (adicCompletion F v)) 0 1) ∈
      (adicCompletionIntegers F v) := GL2.v_le_one_of_mem_localFullLevel _ hg_loc_mem 0 1
  have hg_loc_val : g_loc = Matrix.GeneralLinearGroup.GL2.unipotent
      ((α : v.adicCompletion F)⁻¹ *
        ((t_j : adicCompletion F v) + -(t_i : adicCompletion F v))) :=
    Local.GL2.unipotent_mul_diag_inv_mul_self α hα t_i t_j
  have h01_eq : ((g_loc : GL (Fin 2) (adicCompletion F v)) 0 1) =
      (α : v.adicCompletion F)⁻¹ *
        ((t_j : adicCompletion F v) + -(t_i : adicCompletion F v)) := by
    rw [hg_loc_val]
    simp [Matrix.GeneralLinearGroup.GL2.unipotent, Matrix.unitOfDetInvertible]
  rw [h01_eq] at h01_int
  change i = j
  rw [← (QuotientAddGroup.out_eq' i), ← (QuotientAddGroup.out_eq' j)]
  apply QuotientAddGroup.eq.mpr
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨⟨_, h01_int⟩, ?_⟩
  apply (Subtype.coe_inj).mp
  push_cast
  rw [mul_comm ((α : adicCompletion F v)⁻¹) _, mul_assoc,
    inv_mul_cancel₀ ((Subtype.coe_ne_coe).mpr hα), mul_one]
  simp [t_i, t_j, add_comm]; rfl

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma surjOn_leftCoset_doubleCoset (hv : v ∈ S) :
    Set.SurjOn QuotientGroup.mk (unipotent_mul_diag_image r α hα) (doubleCoset r S α hα) := by
  rintro _ ⟨_, ⟨u, hu, _, rfl, rfl⟩, rfl⟩
  obtain ⟨w, hw_mem, hw_eq⟩ := Subgroup.mem_map.mp hu
  set g_loc : GL (Fin 2) (adicCompletion F v) :=
    FiniteAdeleRing.GL2.toAdicCompletion v w with hg_loc_def
  have hg_loc_tame : g_loc ∈ GL2.localTameLevel v := hw_mem.2 v hv
  have hlocal_target :
      QuotientGroup.mk (g_loc * Local.GL2.diag α hα) ∈ Local.doubleCoset v α hα :=
    ⟨_, Set.mul_mem_mul hg_loc_tame rfl, rfl⟩
  obtain ⟨t, _, ht⟩ :=
    Local.Internal.surjOn_leftCoset_doubleCoset α hα hlocal_target
  have hlocal_ratio :
      (Local.GL2.unipotent_mul_diag α hα
          (Quotient.out t : adicCompletionIntegers F v))⁻¹ *
        (g_loc * Local.GL2.diag α hα) ∈ Local.U1 v :=
    QuotientGroup.eq.mp ht
  refine ⟨unipotent_mul_diag r α hα t, ⟨t, trivial, rfl⟩, ?_⟩
  apply QuotientGroup.eq.mpr
  refine Subgroup.mem_map.mpr ?_
  set W : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    (FiniteAdeleRing.GL2.restrictedProduct.symm
      (RestrictedProduct.mulSingle _ v
        (Local.GL2.unipotent_mul_diag α hα
          (Quotient.out t : adicCompletionIntegers F v))))⁻¹ *
    (w * FiniteAdeleRing.GL2.restrictedProduct.symm
      (RestrictedProduct.mulSingle _ v (Local.GL2.diag α hα))) with hW_def
  refine ⟨W, ?_, ?_⟩
  · refine ⟨fun w_place => ?_, fun w_place hwS => ?_⟩
    · by_cases hwv : w_place = v
      · subst hwv
        rw [hW_def]
        simp only [map_mul, map_inv]
        rw [toAdicCompletion_symm_mulSingle_self w_place _,
          toAdicCompletion_symm_mulSingle_self w_place _]
        exact hlocal_ratio.1
      · rw [hW_def]
        simp only [map_mul, map_inv]
        rw [toAdicCompletion_symm_mulSingle_of_ne hwv _,
          toAdicCompletion_symm_mulSingle_of_ne hwv _]
        simp only [inv_one, one_mul, mul_one]
        exact hw_mem.1 w_place
    · by_cases hwv : w_place = v
      · subst hwv
        rw [hW_def]
        simp only [map_mul, map_inv]
        rw [toAdicCompletion_symm_mulSingle_self w_place _,
          toAdicCompletion_symm_mulSingle_self w_place _]
        exact hlocal_ratio
      · rw [hW_def]
        simp only [map_mul, map_inv]
        rw [toAdicCompletion_symm_mulSingle_of_ne hwv _,
          toAdicCompletion_symm_mulSingle_of_ne hwv _]
        simp only [inv_one, one_mul, mul_one]
        exact hw_mem.2 w_place hwS
  · rw [← hw_eq]
    change Units.map r.symm.toMonoidHom W =
      (unipotent_mul_diag r α hα t)⁻¹ *
        (Units.map r.symm.toMonoidHom w * diag r α hα)
    rw [hW_def]
    simp only [map_mul, map_inv]
    rfl

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
theorem bijOn_leftCoset_doubleCoset (hv : v ∈ S) :
    (unipotent_mul_diag_image r α hα).BijOn QuotientGroup.mk (doubleCoset r S α hα) :=
  ⟨mapsTo_leftCoset_doubleCoset r S α hα,
    injOn_leftCoset_doubleCoset r S α hα,
    surjOn_leftCoset_doubleCoset r S α hα hv⟩

omit [IsTotallyReal F] in
lemma unipotent_mul_diag_image_finite :
    (unipotent_mul_diag_image r α hα).Finite := by
  apply (Set.BijOn.finite_iff_finite
    (bijOn_leftCoset_doubleCoset r {v} α hα (Finset.mem_singleton.mpr rfl))).mpr
  unfold doubleCoset
  exact (QuotientGroup.mk_image_finite_of_compact_of_open
    (Internal.U1_compact r {v}) (Internal.U1_open r {v}))

set_option maxHeartbeats 400000 in
-- Two cosets-rep cases (swap / unipotent), each with a rigidification-roundtrip `h_eq`
-- that unfolds the global representative through `Units.mapEquiv` and `mulSingle`.
omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma mapsTo_T_cosets_doubleCoset (hv : v ∉ S) :
    Set.MapsTo QuotientGroup.mk (HeckeOperator.GoodPrime.T_cosets_image (r := r) v)
      (doubleCoset r S
        (HeckeOperator.GoodPrime.uniformizerInt (F := F) v)
        (HeckeOperator.GoodPrime.uniformizerInt_ne_zero (F := F) v)) := by
  let π : v.adicCompletionIntegers F := HeckeOperator.GoodPrime.uniformizerInt (F := F) v
  let hπ : π ≠ 0 := HeckeOperator.GoodPrime.uniformizerInt_ne_zero (F := F) v
  rintro _ ⟨t, _, rfl⟩
  cases t with
  | none =>
      set u_glob : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
        Units.mapEquiv r.symm.toMulEquiv
          (FiniteAdeleRing.GL2.restrictedProduct.symm
            (RestrictedProduct.mulSingle _ _
              (Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1)))
        with hu_glob_def
      have hu_glob_mem : u_glob ∈ U1 r S := by
        refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
        refine ⟨fun w => ?_, fun w hwS => ?_⟩
        · by_cases hwv : w = v
          · subst hwv
            rw [toAdicCompletion_symm_mulSingle_self w _]
            exact Local.GL2.Internal.swap_mem_localFullLevel (v := w)
          · rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
            exact (GL2.localFullLevel w).one_mem
        · by_cases hwv : w = v
          · subst hwv
            rw [toAdicCompletion_symm_mulSingle_self w _]
            exact absurd hwS hv
          · rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
            exact (GL2.localTameLevel w).one_mem
      have h_eq : GoodPrime.swap_mul_diag (r := r) v = u_glob * diag r π hπ := by
        rw [hu_glob_def]
        unfold GoodPrime.swap_mul_diag diag
        rw [← map_mul, ← map_mul, ← RestrictedProduct.mulSingle_mul]
      refine ⟨u_glob * diag r π hπ, Set.mul_mem_mul hu_glob_mem rfl, ?_⟩
      rw [← h_eq, GoodPrime.goodPrimeRep]
  | some i =>
      set u_glob : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
        Units.mapEquiv r.symm.toMulEquiv
          (FiniteAdeleRing.GL2.restrictedProduct.symm
            (RestrictedProduct.mulSingle _ _
              (Matrix.GeneralLinearGroup.GL2.unipotent
                ((Quotient.out i : adicCompletionIntegers F v) :
                  adicCompletion F v))))
        with hu_glob_def
      have hu_glob_mem : u_glob ∈ U1 r S := by
        refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
        refine ⟨fun w => ?_, fun w _ => ?_⟩
        · by_cases hwv : w = v
          · subst hwv
            rw [toAdicCompletion_symm_mulSingle_self w _]
            exact (Local.GL2.unipotent_mem_U1 (v := w) (Quotient.out i)).1
          · rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
            exact (GL2.localFullLevel w).one_mem
        · by_cases hwv : w = v
          · subst hwv
            rw [toAdicCompletion_symm_mulSingle_self w _]
            exact Local.GL2.unipotent_mem_U1 (v := w) (Quotient.out i)
          · rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
            exact (GL2.localTameLevel w).one_mem
      have h_eq : GoodPrime.unipotent_mul_diag (r := r) v π hπ i = u_glob * diag r π hπ := by
        rw [hu_glob_def]
        unfold GoodPrime.unipotent_mul_diag diag
        rw [← map_mul, ← map_mul, ← RestrictedProduct.mulSingle_mul]
        rfl
      refine ⟨u_glob * diag r π hπ, Set.mul_mem_mul hu_glob_mem rfl, ?_⟩
      rw [← h_eq, GoodPrime.goodPrimeRep]

set_option maxHeartbeats 400000 in
-- The `simp` at the end is flexible: `cases t <;> cases t'` lands on different normal
-- forms (swap-swap, swap-unipotent, ...), so the actual rewrites differ per case.
set_option linter.flexible false in
omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma injOn_T_cosets_doubleCoset :
    Set.InjOn (QuotientGroup.mk (s := U1 r S))
      (HeckeOperator.GoodPrime.T_cosets_image (r := r) v) := by
  rintro _ ⟨t, _, rfl⟩ _ ⟨t', _, rfl⟩ h
  have hU : (GoodPrime.goodPrimeRep (r := r) v t)⁻¹ *
      GoodPrime.goodPrimeRep (r := r) v t' ∈ U1 r S :=
    QuotientGroup.eq.mp h
  obtain ⟨W, hWmem, hWeq⟩ := Subgroup.mem_map.mp hU
  have hWv := hWmem.1 v
  have hmap_symm (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      (Units.map
        (r.toMulEquiv :
          (D ⊗[F] FiniteAdeleRing (𝓞 F) F) →*
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
        ((Units.mapEquiv (AlgEquiv.symm r).toMulEquiv) x) = x := by
    ext
    simp
  have hW_eq' : W = Units.map r.toMonoidHom
      ((GoodPrime.goodPrimeRep (r := r) v t)⁻¹ *
        GoodPrime.goodPrimeRep (r := r) v t') := by
    rw [← hWeq]
    ext
    simp
  have hlocal :
      Local.Internal.Full.cosetReps (v := v) t =
        Local.Internal.Full.cosetReps (v := v) t' := by
    rw [hW_eq'] at hWv
    simp only [map_mul, map_inv] at hWv
    cases t <;> cases t' <;>
      simp [Local.Internal.Full.cosetReps,
        Local.Internal.Full.swapCoset,
        Local.Internal.Full.leftCoset, GoodPrime.goodPrimeRep,
        GoodPrime.swap_mul_diag, GoodPrime.unipotent_mul_diag, hmap_symm,
        toAdicCompletion_symm_mulSingle_self] at hWv ⊢
    all_goals exact QuotientGroup.eq.mpr hWv
  have ht :=
    Local.Internal.Full.injOn_cosetReps (v := v) trivial trivial hlocal
  rw [ht]

set_option maxHeartbeats 400000 in
-- Two surj-cases (swap / unipotent), each builds a global witness `W` over GL2.TameLevel
-- with per-place checks and a closing rigidification `simp only [map_mul, map_inv]; rfl`.
omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma surjOn_T_cosets_doubleCoset (hv : v ∉ S) :
    Set.SurjOn QuotientGroup.mk (HeckeOperator.GoodPrime.T_cosets_image (r := r) v)
      (doubleCoset r S
        (HeckeOperator.GoodPrime.uniformizerInt (F := F) v)
        (HeckeOperator.GoodPrime.uniformizerInt_ne_zero (F := F) v)) := by
  let π : v.adicCompletionIntegers F := HeckeOperator.GoodPrime.uniformizerInt (F := F) v
  let hπ : π ≠ 0 := HeckeOperator.GoodPrime.uniformizerInt_ne_zero (F := F) v
  rintro _ ⟨_, ⟨u, hu, _, rfl, rfl⟩, rfl⟩
  obtain ⟨w, hw_mem, hw_eq⟩ := Subgroup.mem_map.mp hu
  set g_loc : GL (Fin 2) (adicCompletion F v) :=
    FiniteAdeleRing.GL2.toAdicCompletion v w with hg_loc_def
  have hg_loc_full : g_loc ∈ GL2.localFullLevel v := hw_mem.1 v
  have hlocal_target :
      QuotientGroup.mk (g_loc * Local.GL2.diag π hπ) ∈
        Local.Internal.Full.doubleCoset (v := v) :=
    ⟨_, Set.mul_mem_mul hg_loc_full rfl, rfl⟩
  obtain ⟨idx, _, hidx⟩ :=
    Local.Internal.Full.surjOn_cosetReps_doubleCoset
      (v := v) hlocal_target
  cases idx with
  | none =>
      have hidx' :
          QuotientGroup.mk (s := GL2.localFullLevel v)
            (Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1 *
              Local.GL2.diag π hπ) =
          QuotientGroup.mk (s := GL2.localFullLevel v) (g_loc * Local.GL2.diag π hπ) := by
        simpa [Local.Internal.Full.cosetReps] using hidx
      have hlocal_ratio :
          (Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1 *
            Local.GL2.diag π hπ)⁻¹ *
            (g_loc * Local.GL2.diag π hπ) ∈ GL2.localFullLevel v :=
        QuotientGroup.eq.mp hidx'
      refine ⟨GoodPrime.swap_mul_diag (r := r) v, ⟨none, trivial, rfl⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      refine Subgroup.mem_map.mpr ?_
      set W : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v
            (Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1 *
              Local.GL2.diag π hπ)))⁻¹ *
        (w * FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v (Local.GL2.diag π hπ))) with hW_def
      refine ⟨W, ?_, ?_⟩
      · refine ⟨fun w_place => ?_, fun w_place hwS => ?_⟩
        · by_cases hwv : w_place = v
          · subst hwv
            rw [hW_def]
            simp only [map_mul, map_inv]
            rw [toAdicCompletion_symm_mulSingle_self
              w_place _,
              toAdicCompletion_symm_mulSingle_self
                w_place _]
            exact hlocal_ratio
          · rw [hW_def]
            simp only [map_mul, map_inv]
            rw [toAdicCompletion_symm_mulSingle_of_ne hwv _,
              toAdicCompletion_symm_mulSingle_of_ne hwv _]
            simp only [inv_one, one_mul, mul_one]
            exact hw_mem.1 w_place
        · by_cases hwv : w_place = v
          · subst hwv; exact absurd hwS hv
          · rw [hW_def]
            simp only [map_mul, map_inv]
            rw [toAdicCompletion_symm_mulSingle_of_ne hwv _,
              toAdicCompletion_symm_mulSingle_of_ne hwv _]
            simp only [inv_one, one_mul, mul_one]
            exact hw_mem.2 w_place hwS
      · rw [← hw_eq]
        change Units.map r.symm.toMonoidHom W =
          (GoodPrime.swap_mul_diag (r := r) v)⁻¹ *
            (Units.map r.symm.toMonoidHom w * diag r π hπ)
        rw [hW_def]
        simp only [map_mul, map_inv]
        rfl
  | some t =>
      have hidx' :
          QuotientGroup.mk (s := GL2.localFullLevel v)
            (Local.GL2.unipotent_mul_diag π hπ
              (Quotient.out t : adicCompletionIntegers F v)) =
          QuotientGroup.mk (s := GL2.localFullLevel v) (g_loc * Local.GL2.diag π hπ) := by
        simpa [Local.Internal.Full.cosetReps] using hidx
      have hlocal_ratio :
          (Local.GL2.unipotent_mul_diag π hπ
              (Quotient.out t : adicCompletionIntegers F v))⁻¹ *
            (g_loc * Local.GL2.diag π hπ) ∈ GL2.localFullLevel v :=
        QuotientGroup.eq.mp hidx'
      refine ⟨GoodPrime.unipotent_mul_diag (r := r) v π hπ t, ⟨some t, trivial, rfl⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      refine Subgroup.mem_map.mpr ?_
      set W : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v
            (Local.GL2.unipotent_mul_diag π hπ
              (Quotient.out t : adicCompletionIntegers F v))))⁻¹ *
        (w * FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v (Local.GL2.diag π hπ))) with hW_def
      refine ⟨W, ?_, ?_⟩
      · refine ⟨fun w_place => ?_, fun w_place hwS => ?_⟩
        · by_cases hwv : w_place = v
          · subst hwv
            rw [hW_def]
            simp only [map_mul, map_inv]
            rw [toAdicCompletion_symm_mulSingle_self
              w_place _,
              toAdicCompletion_symm_mulSingle_self
                w_place _]
            exact hlocal_ratio
          · rw [hW_def]
            simp only [map_mul, map_inv]
            rw [toAdicCompletion_symm_mulSingle_of_ne hwv _,
              toAdicCompletion_symm_mulSingle_of_ne hwv _]
            simp only [inv_one, one_mul, mul_one]
            exact hw_mem.1 w_place
        · by_cases hwv : w_place = v
          · subst hwv; exact absurd hwS hv
          · rw [hW_def]
            simp only [map_mul, map_inv]
            rw [toAdicCompletion_symm_mulSingle_of_ne hwv _,
              toAdicCompletion_symm_mulSingle_of_ne hwv _]
            simp only [inv_one, one_mul, mul_one]
            exact hw_mem.2 w_place hwS
      · rw [← hw_eq]
        change Units.map r.symm.toMonoidHom W =
          (GoodPrime.unipotent_mul_diag r v π hπ t)⁻¹ *
            (Units.map r.symm.toMonoidHom w * diag r π hπ)
        rw [hW_def]
        simp only [map_mul, map_inv]
        rfl

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private theorem bijOn_T_cosets_doubleCoset (hv : v ∉ S) :
    (HeckeOperator.GoodPrime.T_cosets_image (r := r) v).BijOn
      QuotientGroup.mk
        (doubleCoset r S
          (HeckeOperator.GoodPrime.uniformizerInt (F := F) v)
          (HeckeOperator.GoodPrime.uniformizerInt_ne_zero (F := F) v)) :=
  ⟨mapsTo_T_cosets_doubleCoset r S hv,
    injOn_T_cosets_doubleCoset r S,
    surjOn_T_cosets_doubleCoset r S hv⟩

namespace Internal

omit [IsTotallyReal F] in
lemma T_comm_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (hw : w ∉ S)
    (hvw : v ≠ w) :
    HeckeOperator.T (F := F) (D := D) (S := S) r R v ∘ₗ
      HeckeOperator.T (F := F) (D := D) (S := S) r R w =
    HeckeOperator.T (F := F) (D := D) (S := S) r R w ∘ₗ
      HeckeOperator.T (F := F) (D := D) (S := S) r R v := by
  simpa [HeckeOperator.T] using
    (AbstractHeckeOperator.comm
      (R := R)
      (U := U1 r S)
      (g₁ := Units.mapEquiv r.symm.toMulEquiv
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v
            (Local.GL2.diag (Local.uniformizerInt (F := F) v)
              (Local.Internal.uniformizerInt_ne_zero (F := F) v)))))
      (g₂ := Units.mapEquiv r.symm.toMulEquiv
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ w
            (Local.GL2.diag (Local.uniformizerInt (F := F) w)
              (Local.Internal.uniformizerInt_ne_zero (F := F) w)))))
      (h₁ := QuotientGroup.mk_image_finite_of_compact_of_open
        (WeightTwoAutomorphicForm.Internal.U1_compact r S)
        (WeightTwoAutomorphicForm.Internal.U1_open r S))
      (h₂ := QuotientGroup.mk_image_finite_of_compact_of_open
        (WeightTwoAutomorphicForm.Internal.U1_compact r S)
        (WeightTwoAutomorphicForm.Internal.U1_open r S))
      (hcomm := by
        refine ⟨HeckeOperator.GoodPrime.T_cosets_image (r := r) v,
          HeckeOperator.GoodPrime.T_cosets_image (r := r) w, ?_, ?_, ?_⟩
        · simpa [HeckeOperator.GoodPrime.T_cosets_image, doubleCoset, U1, diag] using
            (bijOn_T_cosets_doubleCoset (r := r) (S := S) (v := v) hv)
        · simpa [HeckeOperator.GoodPrime.T_cosets_image, doubleCoset, U1, diag] using
            (bijOn_T_cosets_doubleCoset (r := r) (S := S) (v := w) hw)
        · intro a ha b hb
          exact HeckeOperator.GoodPrime.goodPrimeRep_commute_of_ne (r := r) hvw a ha b hb))

end Internal

omit [IsTotallyReal F] in
lemma quot_top_finite (r : Rigidification F D) (α : v.adicCompletionIntegers F) (hα : α ≠ 0) :
    (⊤ : Set ((adicCompletionIntegers F v) ⧸ (Ideal.span {α}))).Finite := by
  apply Set.Finite.of_finite_image _ (unipotent_mul_diag_inj r α hα)
  apply unipotent_mul_diag_image_finite

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma goodPrimeRep_commute_with_unipotent_of_ne
    {v w : HeightOneSpectrum (𝓞 F)} (hvw : v ≠ w)
    (a : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ)
    (ha : a ∈ HeckeOperator.GoodPrime.goodPrimeRep_image (r := r) v)
    {β : w.adicCompletionIntegers F} (hβ : β ≠ 0)
    (b : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) (hb : b ∈ unipotent_mul_diag_image r β hβ) :
    a * b = b * a := by
  rcases ha with ⟨x, _, rfl⟩
  rcases hb with ⟨t, _, rfl⟩
  cases x <;>
    exact ((RestrictedProduct.mulSingle_commute
        (i := v) (j := w) hvw _ _).map
      (FiniteAdeleRing.GL2.restrictedProduct (F := F)).symm.toMonoidHom |>.map
      (Units.mapEquiv r.symm.toMulEquiv).toMonoidHom).eq

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma unipotent_mul_diag_commute_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hvw : v ≠ w)
    {α : v.adicCompletionIntegers F} (hα : α ≠ 0)
    {β : w.adicCompletionIntegers F} (hβ : β ≠ 0)
    (a : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) (ha : a ∈ unipotent_mul_diag_image r α hα)
    (b : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) (hb : b ∈ unipotent_mul_diag_image r β hβ) :
    a * b = b * a := by
  rcases ha with ⟨t, _, rfl⟩
  rcases hb with ⟨u, _, rfl⟩
  exact ((RestrictedProduct.mulSingle_commute
      (i := v) (j := w) hvw _ _).map
    (FiniteAdeleRing.GL2.restrictedProduct (F := F)).symm.toMonoidHom |>.map
    (Units.mapEquiv r.symm.toMulEquiv).toMonoidHom).eq

/-- The Hecke operator U_{v,α} associated to the matrix (α 0;0 1) at v,
considered as an R-linear map from R-valued quaternionic weight 2
automorphic forms of level U_1(S). Here α is a nonzero element of 𝓞ᵥ.
We do not demand the condition v ∈ S, the bad primes, but this operator
should only be used in this setting. See also `T r v` for the good primes.
-/
noncomputable def U :
    WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
    WeightTwoAutomorphicFormOfLevel (U1 r S) R :=
  AbstractHeckeOperator.HeckeOperator (R := R) (diag r α hα) (U1 r S) (U1 r S)
  (QuotientGroup.mk_image_finite_of_compact_of_open
    (WeightTwoAutomorphicForm.Internal.U1_compact r S)
    (WeightTwoAutomorphicForm.Internal.U1_open r S))

lemma _root_.Ne.mul {M₀ : Type*} [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}
  (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := mul_ne_zero ha hb

noncomputable instance :
    DistribSMul (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ (WeightTwoAutomorphicForm F D R) :=
  distribMulAction.toDistribSMul

omit [IsTotallyReal F] in
lemma U_apply (a : WeightTwoAutomorphicFormOfLevel (U1 r S) R) :
    ((U r S R α hα) a).1 =
    ∑ᶠ (gᵢ : (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) (_ : gᵢ ∈ Quotient.out '' (doubleCoset r S α hα)),
      gᵢ • a.1 :=
  rfl

open AbstractHeckeOperator in
omit [IsTotallyReal F] in
private lemma U_apply_eq_finsum_unipotent_mul_diag_image (hv : v ∈ S)
    (a : WeightTwoAutomorphicFormOfLevel (U1 r S) R) :
    ((U r S R α hα) a).1 =
    ∑ᶠ (g : (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) (_ : g ∈ unipotent_mul_diag_image r α hα),
      g • a.1 :=
  (eq_finsum_quotient_out_of_bijOn' a (bijOn_leftCoset_doubleCoset r S α hα hv)) ▸
    U_apply r S R α hα a

/-- A "raw lift" version of `unipotent_mul_diag`: takes an arbitrary `t : 𝓞_v` instead of
a coset class. This is useful for manipulating products via the local matrix formula. -/
private noncomputable def unipotent_mul_diag_lift (t : adicCompletionIntegers F v) :
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Units.mapEquiv r.symm.toMulEquiv
    (FiniteAdeleRing.GL2.restrictedProduct.symm
    (RestrictedProduct.mulSingle _ _
      (Local.GL2.unipotent_mul_diag α hα t)))

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
private lemma unipotent_mul_diag_eq_lift (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α})) :
    unipotent_mul_diag r α hα t = unipotent_mul_diag_lift r α hα (Quotient.out t) :=
  rfl

omit [IsTotallyReal F] [IsQuaternionAlgebra F D] in
/-- The global multiplication formula for `unipotent_mul_diag_lift`: matches the local
matrix product formula `!![α,s;0,1] * !![β,t;0,1] = !![αβ, α*t+s; 0,1]`, transported
through the restricted product + rigidification pipeline. -/
private lemma unipotent_mul_diag_lift_mul {β : v.adicCompletionIntegers F} (hβ : β ≠ 0)
    (s t : adicCompletionIntegers F v) :
    unipotent_mul_diag_lift r α hα s * unipotent_mul_diag_lift r β hβ t =
    unipotent_mul_diag_lift r (α * β) (mul_ne_zero hα hβ)
      ((α : adicCompletionIntegers F v) * t + s) := by
  simp only [unipotent_mul_diag_lift, ← map_mul, ← RestrictedProduct.mulSingle_mul]
  congr 3
  exact Local.GL2.Internal.unipotent_mul_diag_mul α hα hβ s t

set_option maxHeartbeats 400000 in
-- The proof rewrites a `smul` equality through `mulSingle_mul` and `map_mul` after
-- constructing a `U1 r S` witness from the divisibility hypothesis.
omit [IsTotallyReal F] in
/-- `U1`-invariance of `unipotent_mul_diag_lift` action: if `t₁ - t₂ ∈ (γ)`, then
`unipotent_mul_diag_lift γ t₁ • a = unipotent_mul_diag_lift γ t₂ • a` for any
`U1 r S`-fixed automorphic form `a`. -/
private lemma unipotent_mul_diag_lift_smul_eq {γ : v.adicCompletionIntegers F} (hγ : γ ≠ 0)
    {t₁ t₂ : v.adicCompletionIntegers F}
    (h : t₁ - t₂ ∈ Ideal.span ({γ} : Set (v.adicCompletionIntegers F)))
    (a : WeightTwoAutomorphicFormOfLevel (U1 r S) R) :
    unipotent_mul_diag_lift r γ hγ t₁ • a.1 =
      unipotent_mul_diag_lift r γ hγ t₂ • a.1 := by
  -- Strategy: write `lift t₁ = lift t₂ * u''` where `u'' = (lift t₂)⁻¹ * lift t₁ ∈ U1 r S`.
  -- Then `lift t₁ • a = lift t₂ • (u'' • a) = lift t₂ • a` using `a.2` on `u''`.
  set u'' : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
    (unipotent_mul_diag_lift r γ hγ t₂)⁻¹ * unipotent_mul_diag_lift r γ hγ t₁ with hu''_def
  -- Obtain the ring element `m` with `t₁ - t₂ = m * γ`.
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp h
  -- Show `u''` is in `U1 r S` by exhibiting a witness in `GL2.TameLevel S`.
  have hu'' : u'' ∈ U1 r S := by
    refine Subgroup.mem_map.mpr ⟨?_, ?_, ?_⟩
    · -- The witness: the unit built from `mulSingle v (unipotent ↑m)`.
      exact FiniteAdeleRing.GL2.restrictedProduct.symm
        (RestrictedProduct.mulSingle _ _
          (Matrix.GeneralLinearGroup.GL2.unipotent (m : adicCompletion F v)))
    · -- The witness is in `GL2.TameLevel S`.
      refine ⟨?_, ?_⟩
      · intro w
        -- At every place `w`, the element is in `localFullLevel w`.
        by_cases hwv : w = v
        · subst hwv
          rw [toAdicCompletion_symm_mulSingle_self w _]
          exact (Local.GL2.unipotent_mem_U1 (v := w) m).1
        · -- The image at `w ≠ v` is `1`, which is in `localFullLevel`.
          rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
          exact (GL2.localFullLevel w).one_mem
      · intro w hwS
        by_cases hwv : w = v
        · subst hwv
          rw [toAdicCompletion_symm_mulSingle_self w _]
          exact Local.GL2.unipotent_mem_U1 (v := w) m
        · rw [toAdicCompletion_symm_mulSingle_of_ne hwv _]
          exact (GL2.localTameLevel w).one_mem
    · -- Applying `Units.map r.symm.toMonoidHom` to the witness yields `u''`.
      change Units.map r.symm.toMonoidHom _ = u''
      rw [hu''_def, unipotent_mul_diag_lift, unipotent_mul_diag_lift]
      change _ = (Units.mapEquiv r.symm.toMulEquiv _)⁻¹ *
        (Units.mapEquiv r.symm.toMulEquiv _)
      rw [← map_inv, ← map_mul]
      change Units.mapEquiv r.symm.toMulEquiv _ =
        Units.mapEquiv r.symm.toMulEquiv _
      congr 1
      rw [← map_inv, ← map_mul, ← RestrictedProduct.mulSingle_inv,
        ← RestrictedProduct.mulSingle_mul]
      congr 1
      rw [Local.GL2.unipotent_mul_diag_inv_mul_self γ hγ t₂ t₁]
      congr 1
      -- Need: `(γ : adicCompletion F v)⁻¹ * (t₁ + -t₂) = m` (in `adicCompletion F v`).
      have hmval : ((t₁ : adicCompletion F v) + -(t₂ : adicCompletion F v)) =
          ((γ : adicCompletion F v)) * (m : adicCompletion F v) := by
        have hh : ((m : adicCompletion F v)) * (γ : adicCompletion F v) =
            (t₁ : adicCompletion F v) - (t₂ : adicCompletion F v) := by
          have := congrArg (fun x : v.adicCompletionIntegers F =>
            (x : adicCompletion F v)) hm
          push_cast at this
          exact this
        linear_combination -hh
      have hγne : (γ : adicCompletion F v) ≠ 0 := by exact_mod_cast hγ
      rw [hmval, ← mul_assoc, inv_mul_cancel₀ hγne, one_mul]
  -- Rewrite `lift t₁ = lift t₂ * u''`.
  have hlift : unipotent_mul_diag_lift r γ hγ t₁ =
      unipotent_mul_diag_lift r γ hγ t₂ * u'' := by
    rw [hu''_def, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hlift, mul_smul]
  -- Use `U1`-invariance of `a`.
  congr 1
  exact a.2 ⟨u'', hu''⟩

omit [IsTotallyReal F] in
lemma U_mul_aux {v : HeightOneSpectrum (𝓞 F)}
    {α β : v.adicCompletionIntegers F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (a : WeightTwoAutomorphicFormOfLevel (U1 r S) R) :
    ∑ᶠ (i : (adicCompletionIntegers F v) ⧸ Ideal.span {α})
      (j : (adicCompletionIntegers F v) ⧸ Ideal.span {β}),
      unipotent_mul_diag r α hα i • unipotent_mul_diag r β hβ j • a.1 =
    ∑ᶠ (k : (adicCompletionIntegers F v) ⧸ Ideal.span {α * β}),
      unipotent_mul_diag r (α * β) (hα.mul hβ) k • a.1 :=
by
  -- All three quotients are finite (deduced from `quot_top_finite`).
  have hfinα : Finite (v.adicCompletionIntegers F ⧸ Ideal.span ({α} : Set _)) := by
    have := (quot_top_finite r α hα)
    rw [Set.top_eq_univ, Set.finite_univ_iff] at this; exact this
  have hfinβ : Finite (v.adicCompletionIntegers F ⧸ Ideal.span ({β} : Set _)) := by
    have := (quot_top_finite r β hβ)
    rw [Set.top_eq_univ, Set.finite_univ_iff] at this; exact this
  have hfinαβ :
      Finite (v.adicCompletionIntegers F ⧸ Ideal.span ({α * β} : Set _)) := by
    have := (quot_top_finite r (α * β) (mul_ne_zero hα hβ))
    rw [Set.top_eq_univ, Set.finite_univ_iff] at this; exact this
  -- Combine the double finsum into one over the product, then transport via the bijection
  -- `prodEquivSpanMul`, and identify summands using the U1-invariance lemma.
  set Qα := v.adicCompletionIntegers F ⧸ Ideal.span ({α} : Set _) with hQα
  set Qβ := v.adicCompletionIntegers F ⧸ Ideal.span ({β} : Set _) with hQβ
  rw [show (∑ᶠ (i : Qα) (j : Qβ),
      unipotent_mul_diag r α hα i • unipotent_mul_diag r β hβ j • a.1) =
    ∑ᶠ (p : Qα × Qβ),
      unipotent_mul_diag r α hα p.1 • unipotent_mul_diag r β hβ p.2 • a.1 from
    (finsum_curry (α := Qα) (β := Qβ)
      (fun p => unipotent_mul_diag r α hα p.1 • unipotent_mul_diag r β hβ p.2 • a.1)
      (Set.toFinite _)).symm]
  have hαreg : IsLeftRegular α := (IsRegular.of_ne_zero hα).left
  rw [← finsum_comp_equiv (Ideal.Quotient.prodEquivSpanMul hαreg β)
    (f := fun (k : v.adicCompletionIntegers F ⧸ Ideal.span {α * β}) =>
      unipotent_mul_diag r (α * β) (hα.mul hβ) k • a.1)]
  refine finsum_congr (fun p => ?_)
  obtain ⟨i, j⟩ := p
  rw [unipotent_mul_diag_eq_lift, unipotent_mul_diag_eq_lift, ← mul_smul,
    unipotent_mul_diag_lift_mul, unipotent_mul_diag_eq_lift]
  apply unipotent_mul_diag_lift_smul_eq
  change (α * j.out + i.out) -
    (Ideal.Quotient.prodEquivSpanMul hαreg β (i, j)).out ∈
      Ideal.span ({α * β} : Set _)
  have h1 :
      (Ideal.Quotient.prodEquivSpanMul hαreg β (i, j)).out - (i.out + α * j.out)
        ∈ Ideal.span ({α * β} : Set _) := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out,
      Ideal.Quotient.prodEquivSpanMul_apply]
  have heq : (α * j.out + i.out) -
      (Ideal.Quotient.prodEquivSpanMul hαreg β (i, j)).out =
      -((Ideal.Quotient.prodEquivSpanMul hαreg β (i, j)).out -
        (i.out + α * j.out)) := by ring
  rw [heq]; exact neg_mem h1

open AbstractHeckeOperator in
omit [IsTotallyReal F] in
private lemma U_mul {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S)
    {α β : v.adicCompletionIntegers F} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (U r S R α hα ∘ₗ U r S R β hβ) =
    U r S R (α * β) (hα.mul hβ) := by
  ext1 a
  apply (Subtype.coe_inj).mp
  simp only [U_apply_eq_finsum_unipotent_mul_diag_image _ _ _ _ _ hv,
    LinearMap.coe_comp, Function.comp_apply,
    smul_finsum_mem (unipotent_mul_diag_image_finite r β hβ)]
  unfold unipotent_mul_diag_image
  simp only [finsum_mem_image (unipotent_mul_diag_inj _ _ _)]
  simpa using U_mul_aux r S R hα hβ a

namespace Internal

omit [IsTotallyReal F] in
lemma U_comm {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S)
    {α β : v.adicCompletionIntegers F} (hα : α ≠ 0) (hβ : β ≠ 0) :
    U r S R α hα ∘ₗ U r S R β hβ =
    U r S R β hβ ∘ₗ U r S R α hα := by
  rw [U_mul _ _ _ hv, U_mul _ _ _ hv]
  congr 1
  rw [mul_comm]

omit [IsTotallyReal F] in
lemma U_comm_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) (hw : w ∈ S)
    (hvw : v ≠ w) {α : v.adicCompletionIntegers F} (hα : α ≠ 0)
    {β : w.adicCompletionIntegers F} (hβ : β ≠ 0) :
    U r S R α hα ∘ₗ U r S R β hβ =
    U r S R β hβ ∘ₗ U r S R α hα := by
  simpa [HeckeOperator.U] using
    (AbstractHeckeOperator.comm
      (R := R)
      (U := U1 r S)
      (g₁ := Units.mapEquiv r.symm.toMulEquiv
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v
            (Local.GL2.diag α hα))))
      (g₂ := Units.mapEquiv r.symm.toMulEquiv
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ w
            (Local.GL2.diag β hβ))))
      (h₁ := QuotientGroup.mk_image_finite_of_compact_of_open
        (WeightTwoAutomorphicForm.Internal.U1_compact r S)
        (WeightTwoAutomorphicForm.Internal.U1_open r S))
      (h₂ := QuotientGroup.mk_image_finite_of_compact_of_open
        (WeightTwoAutomorphicForm.Internal.U1_compact r S)
        (WeightTwoAutomorphicForm.Internal.U1_open r S))
      (hcomm := by
        refine ⟨unipotent_mul_diag_image r α hα, unipotent_mul_diag_image r β hβ, ?_, ?_, ?_⟩
        · simpa [unipotent_mul_diag_image, doubleCoset, U1, diag] using
            (bijOn_leftCoset_doubleCoset (r := r) (S := S) (α := α) (hα := hα) hv)
        · simpa [unipotent_mul_diag_image, doubleCoset, U1, diag] using
            (bijOn_leftCoset_doubleCoset (r := r) (S := S) (α := β) (hα := hβ) hw)
        · intro a ha b hb
          exact unipotent_mul_diag_commute_of_ne (r := r) hvw hα hβ a ha b hb))

omit [IsTotallyReal F] in
lemma T_comm_U_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (hw : w ∈ S)
    (hvw : v ≠ w) {β : w.adicCompletionIntegers F} (hβ : β ≠ 0) :
    HeckeOperator.T (F := F) (D := D) (S := S) r R v ∘ₗ
      U r S R β hβ =
    U r S R β hβ ∘ₗ
      HeckeOperator.T (F := F) (D := D) (S := S) r R v := by
  simpa [HeckeOperator.T, HeckeOperator.U] using
    (AbstractHeckeOperator.comm
      (R := R)
      (U := U1 r S)
      (g₁ := Units.mapEquiv r.symm.toMulEquiv
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ v
            (Local.GL2.diag (Local.uniformizerInt (F := F) v)
              (Local.Internal.uniformizerInt_ne_zero (F := F) v)))))
      (g₂ := Units.mapEquiv r.symm.toMulEquiv
        (FiniteAdeleRing.GL2.restrictedProduct.symm
          (RestrictedProduct.mulSingle _ w
            (Local.GL2.diag β hβ))))
      (h₁ := QuotientGroup.mk_image_finite_of_compact_of_open
        (WeightTwoAutomorphicForm.Internal.U1_compact r S)
        (WeightTwoAutomorphicForm.Internal.U1_open r S))
      (h₂ := QuotientGroup.mk_image_finite_of_compact_of_open
        (WeightTwoAutomorphicForm.Internal.U1_compact r S)
        (WeightTwoAutomorphicForm.Internal.U1_open r S))
      (hcomm := by
        refine ⟨HeckeOperator.GoodPrime.T_cosets_image (r := r) v,
          unipotent_mul_diag_image r β hβ, ?_, ?_, ?_⟩
        · simpa [HeckeOperator.GoodPrime.T_cosets_image, doubleCoset, U1, diag] using
            (bijOn_T_cosets_doubleCoset (r := r) (S := S) (v := v) hv)
        · simpa [unipotent_mul_diag_image, doubleCoset, U1, diag] using
            (bijOn_leftCoset_doubleCoset (r := r) (S := S) (α := β) (hα := hβ) hw)
        · intro a ha b hb
          exact goodPrimeRep_commute_with_unipotent_of_ne (r := r) hvw a ha hβ b hb))

end Internal

end U

end HeckeOperator

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm
