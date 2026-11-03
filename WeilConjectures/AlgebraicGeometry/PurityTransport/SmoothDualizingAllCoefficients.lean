/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # The smooth dualizing complex for every admissible coefficient

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/
_section.md and sk-cor-sp-all-coefficients.proof.md
(blueprint: sk-cor-sp-all-coefficients).

The exceptional inverse image is the restriction of a specified right adjoint on
Loc(Dctf). Coefficient rings, positive Tate lines, and the full Dctf subcategory
are the existing condensed module-object constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The exceptional inverse image of the coefficient unit under a smooth structure
morphism of pure dimension `d` is the native Tate line shifted by `2d`, inside
Dctf. The compactification and its localizing right adjoint are specified, rather
than replaced by an arbitrary functor on the ambient derived category. The output
membership certificates introduce no additional hypotheses.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/
_section.md, entire statement (blueprint: sk-cor-sp-all-coefficients).

The base field is finite or algebraically closed, of positive prime
characteristic distinct from ell; no finite-field datum or Frobenius is chosen.

Proof in words. Apply sk-thm-purity-transport to the structure morphism and the
coefficient unit. The unit has the rank-one finite constant scalar model and Tor
amplitude [0,0], hence is in Dctf. The purity theorem restricts the specified
localizing right adjoint to Dctf and gives its canonical natural comparison with
twisted, shifted pullback. Evaluate this comparison at the unit. By clause (1) of
sk-prop-sfb-cartesian-coefficients the coefficient pullback is exact and its
canonical coefficient comparison identifies the pulled-back unit with the unit
on X. Tensoring by the native Tate line and shifting identifies the source with
Lambda_X(d)[2d]; this is also the existing sourceUnit isomorphism. The source
preservation assertion of purity proves that this shifted line lies in Dctf.
Invert the composite to obtain the displayed orientation. Since Dctf is full,
the ambient comparison and its inverse define the asserted isomorphism in Dctf.
Its naturality is inherited from the natural purity comparison and the canonical
pullback-unit and tensor-unit isomorphisms. This applies to every admissible
coefficient, including nonregular finite rings and the zero ring. -/
theorem smooth_dualizing_all_coefficients
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] (_hk : Finite k ∨ IsAlgClosed k)
    (_hEll : IsUnit (ell : k)) (c : Coefficient ell)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (cf : Compactification X.hom)
    (hL : ∀ K, localizing ell c X.left K → localizing ell c (Spec (.of k))
      ((rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K))
    (G : (localizing ell c (Spec (.of k))).FullSubcategory ⥤
      (localizing ell c X.left).FullSubcategory)
    (_b : localizingLowerShriek (c.obj ell) cf hL ⊣ G) :
    ∃ hU : property ell c (Spec (.of k)) (unit ell c (Spec (.of k))),
    ∃ hG : ∀ K : c.ctf ell (Spec (.of k)),
      property ell c X.left (G.obj ((inclusion ell c (Spec (.of k))).obj K)).obj,
    ∃ hT : property ell c X.left (c.derivedLine ell X.left d),
      Nonempty ((exceptional ell c G hG).obj ⟨unit ell c (Spec (.of k)), hU⟩ ≅
        (⟨c.derivedLine ell X.left d, hT⟩ : c.ctf ell X.left)) := by
  classical
  let s : GeneralPurityTransport.SmoothDatum k :=
    { X := X
      Y := Over.mk (𝟙 (Spec (.of k)))
      yFinite := by change LocallyOfFiniteType (𝟙 _); infer_instance
      yQuasiCompact := by change QuasiCompact (𝟙 _); infer_instance
      ySeparated := by change IsSeparated (𝟙 _); infer_instance
      map := X.hom
      isOver := ⟨by change X.hom ≫ 𝟙 _ = X.hom; simp⟩
      dim := d
      compactification := cf }
  obtain ⟨a, hB, _⟩ := GeneralPurityTransport.smooth_purity_transport ell k _hk _hEll
  obtain ⟨hG, bctf, _, gamma, _⟩ := hB c s hL G _b
  have hU : property ell c (Spec (.of k)) (unit ell c (Spec (.of k))) :=
    constantCoefficientObject_mem (c.obj ell) (Spec (.of k))
  let U : c.ctf ell (Spec (.of k)) := ⟨_, hU⟩
  let e := sourceUnit ell c X.hom d
  have hsource := (a c s).source_closed _ hU
  have : (constantModelBoundedConstructible (c.obj ell) X.left).IsClosedUnderIsomorphisms :=
    (AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined
      (c.obj ell) X.left).2.1
  have hT : property ell c X.left (c.derivedLine ell X.left d) :=
    ⟨ObjectProperty.prop_of_iso _ e hsource.1,
      ObjectProperty.prop_of_iso _ e hsource.2⟩
  refine ⟨hU, hG, hT, ⟨?_⟩⟩
  exact (gamma.app U).symm ≪≫
    (property ell c X.left).fullyFaithfulι.preimageIso e

end AlgebraicGeometry.ProEtale.PurityTransport
