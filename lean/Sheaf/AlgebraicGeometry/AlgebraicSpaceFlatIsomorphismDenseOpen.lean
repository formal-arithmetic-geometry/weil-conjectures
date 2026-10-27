/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.Blowup.Gluing
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # A flat morphism isomorphic over a schematically dense open is an open immersion

Source: Stacks Project, More on Morphisms of Spaces, Tag 0879, lemma-zariski,
hypotheses (1)--(3) (blueprint: lem-sfb-space-flat-isomorphism-dense-open).

Schematic density is sectionwise injectivity of the restriction into the direct image:
regular functions are detected by their restrictions to all charts of the inverse image.
The quasi-coherent ideal and blowup conventions in the node are background conventions;
no ideal or blowup occurs in the hypotheses or conclusion of Tag 0879.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated flat locally finite-type map of algebraic spaces is an open immersion
if it is an isomorphism over a quasi-compact schematically dense open subspace.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0879, lemma-zariski,
hypotheses (1)--(3) (blueprint: lem-sfb-space-flat-isomorphism-dense-open).

Proof:
1. Over V the morphism is an isomorphism, hence locally of finite presentation:
   compatible etale charts are etale over V, so their connecting map is etale by
   lem-trf-space-chartwise-etale-permanence. Etale scheme maps are locally finitely
   presented (def-weil-etale-morphism). Apply
   lem-sfb-space-flat-finite-presentation-dense-open to obtain this property for g.
2. Set P = Y times_T Y. Its first projection is flat by base change of g
   (lem-sfb-space-flat-proper-fp-locality). Twice apply
   lem-sfb-space-flat-pullback-schematic-density, first to g and then to this projection.
   This makes W = P times_T V a quasi-compact schematically dense open in P.
   The fibre-product identifications use lem-trf-space-fibre-products-etale-covers.
3. Separatedness makes the diagonal Y to P a closed immersion. Its quasi-coherent
   ideal I (lem-sfb-space-ideal-closed-subspace-correspondence) restricts to zero on W,
   since there the diagonal is that of an isomorphism. Schematic density says the
   restriction of O_P to W is injective. Thus I is zero, so the ideal correspondence
   identifies the diagonal with P. On scheme-valued sections this says g is a mono.
4. Apply lem-sfb-space-flat-monomorphism-representable: every scheme base change of g
   is a scheme, without needing any extra finiteness or quasi-compactness assumption.
5. Choose a surjective etale scheme atlas U of T (def-trf-algebraic-space). The scheme
   Y_U is etale over Y by lem-trf-space-fibre-products-etale-covers. The chart tests
   def-sfb-space-morphism-properties give flatness and local finite presentation for
   Y_U to U; its monomorphism follows from step 3. Apply
   lem-pe-flat-lfp-monomorphism-open, namely IsOpenImmersion.of_flat_of_mono.
   Descend the open immersion by lem-trf-space-open-immersion-etale-local.
These arguments include the empty spaces and identity open immersions. -/
theorem isOpenImmersion_of_flat_isIso_over_schematicallyDense_open
    {S : Scheme.{u}} {Y T V : AlgebraicSpace S} (g : Y ⟶ T) (j : V ⟶ T)
    (hsep : MapIsSeparated g) (hflat : MapIsFlat g)
    (hlft : MapIsLocally (@LocallyOfFiniteType) g)
    (hj : IsRepresentableWith
      (fun _ _ p ↦ IsOpenImmersion p.left ∧ QuasiCompact p.left) j.hom.hom)
    (hiso : IsIso (Limits.pullback.snd g.hom j.hom))
    (hdense : ∀ (U : T.EtaleSite) (a b : T.structureSheaf.obj.obj (op U)),
      (∀ (W : V.EtaleSite) (p : W.obj.left ⟶ U.obj.left),
        W.obj.hom ≫ j.hom.hom = yoneda.map p ≫ U.obj.hom →
        (Scheme.Γ.map p.left.op).hom a = (Scheme.Γ.map p.left.op).hom b) → a = b) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) g.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
