/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.DivisibleExtensionDerivedReduction
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-!
# Modulus change of normalized derived reduction

Source: blueprint main-20261015, sk-lem-geo-cartier, proof paragraph 4 and its
auxiliary exponent comparison; Stacks Tags 06YY, 0D6D, 07A6 and 0152
(blueprint: lem-geo-cartier-exponent-independence).

The coefficient comparison is constructed by uniqueness of normalized left adjoints.
Its composite-unit characterization is the one of successive derived quotient
normalization. Kernel and quotient presentations and their normalized identifications
are the recorded DivisibleReduction constructions. The extension in a presentation
is auxiliary: for arbitrary B and F one may always take the split extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wZ wM wN
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.GeoCartierExponent

open DivisibleReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {m n : ℕ}

/-- The constant coefficient map induced by reduction from Z/m to Z/n.
Source: Cartier exponent comparison, Stacks 0D6D
(blueprint: lem-geo-cartier-exponent-independence). -/
def residueProjection (h : n ∣ m) : residues J m ⟶ residues J n :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom h (ZMod n)).comp ULift.ringEquiv.toRingHom)))

set_option linter.unusedSectionVars false in
/-- The actual constant coefficient projections form the required triangle.
Source: Stacks 0D6D, Cartier exponent comparison
(blueprint: lem-geo-cartier-exponent-independence).
Proof: both ring homomorphisms send each integer to its residue modulo n.
Integer casts determine homomorphisms out of Z. ULift transports that equality,
and functoriality of constant sheafification preserves the composite. -/
theorem projection_comp (h : n ∣ m) :
    projection J m ≫ residueProjection (J := J) h = projection J n := by
  unfold projection residueProjection
  rw [← Functor.map_comp]
  congr 1
  ext x
  rcases x with ⟨x⟩
  change (ZMod.castHom h (ZMod n)) (x : ZMod m) = (x : ZMod n)
  exact map_intCast _ _

/-- Scalar restriction along the modulus map, retaining the underlying sections.
Source: Stacks 03D7 and 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
abbrev residueRestriction (h : n ∣ m) : Residue J n ⥤ Residue J m :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
    (residueProjection (J := J) h))

/-- The identity-on-sections composition comparison for ordinary restriction.
Source: Stacks 03D7 and 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
def restrictionComp (h : n ∣ m) :
    residueRestriction (J := J) h ⋙ restriction J m ≅ restriction J n :=
  NatIso.ofComponents (fun M ↦
    (fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App
          ((projection J m).hom.app U).hom
          ((residueProjection (J := J) h).hom.app U).hom
          ((projection J n).hom.app U).hom
          (congrArg (fun a ↦ (a.hom.app U).hom) (projection_comp (J := J) h)).symm
          (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

variable [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wM} (Residue J m)] [HasDerivedCategory.{wN} (Residue J n)]

/-- The canonical composition comparison for termwise derived restriction.
Source: Stacks 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
def derivedRestrictionComp (h : n ∣ m) :
    (residueRestriction (J := J) h).mapDerivedCategory ⋙ derivedRestriction m ≅
      derivedRestriction n :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionComp (J := J) h)

/-- The canonical transitivity isomorphism. Normalized adjunctions determine it by
sending the composite scalar-extension unit to the direct scalar-extension unit.
This is exactly the unit characterization of
lem-sfb-successive-derived-quotient-normalization, not a chosen objectwise isomorphism.
Source: Stacks 0D6D and 07A6 (blueprint: lem-geo-cartier-exponent-independence). -/
def transitivity (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h)) :
    Dm.T ⋙ Dmn.T ≅ Dn.T :=
  Adjunction.leftAdjointUniq
    (((sheafScalarDerivedAdjunction (projection J m) Dm).comp
      (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn)).ofNatIsoRight
        (derivedRestrictionComp (J := J) h))
    (sheafScalarDerivedAdjunction (projection J n) Dn)

/-- The canonical K-flat computation on a degree-zero flat module, written as a morphism
so that no flatness proof is hidden in its data. It is invertible for flat M.
Source: Stacks 06YY and 06YQ (blueprint: lem-geo-cartier-exponent-independence). -/
def ordinarySingle (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) :
    Dmn.T.obj ((DerivedCategory.singleFunctor (Residue J m) 0).obj M) ⟶
      (DerivedCategory.singleFunctor (Residue J n) 0).obj
        (changeOfRings (residueProjection (J := J) h) M) :=
  Dmn.ε.app ((CochainComplex.singleFunctor (Residue J m) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex Dmn.E (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctor (Residue J n) 0).map (eqToHom (Dmn.obj_eq M))

/-- Changing modulus identifies the actual transitivity maps with ordinary quotient and
torsion scalar extension. The two presentations encode exactly the kernels/cokernels
and epi/mono hypotheses, with the same underlying B and F identified by hB and hF.
Their auxiliary short exact extensions may both be chosen split.

Source: Cartier proof paragraph 4, auxiliary exponent comparison; Stacks 06YY, 0D6D,
07A6 and 0152 (blueprint: lem-geo-cartier-exponent-independence).
Proof:
1. Resolve F by a flat-term K-flat complex. The multiplication-by-q short exact
sequence and its cohomology sequence identify the degree-zero extension unit with
F -> F/qF, for q=m,n (lem-pc-kflat-resolution, def-pc-flat-sheaf-modules,
lem-weil-pbc-complex-ses-triangle, lem-sf-derived-homology-long-exact,
lem-pur-derived-change-of-rings, lem-pur-sheaf-ring-derived-coefficient-adjunction,
lem-weil-pbc-derived-single-fully-faithful).
2. Use the normalized identifications of lem-sfb-divisible-extension-derived-reduction.
The composite-unit identity of lem-sfb-successive-derived-quotient-normalization
identifies the comparison defined above with its canonical transitivity map.
3. The flat single complexes Q_m[0] and H_m[0] are K-flat by
lem-pc-bounded-above-flat-kflat-site. Derived change of rings computes their extensions
by ordinarySingle. The normalized adjunction unit is x -> 1 tensor x, also after
shifting, and the transpose sends b tensor x to b times its image.
4. The quotient projection Q_m -> Q_n composed with F -> Q_m is F -> Q_n.
The two successive normalized adjunction bijections therefore identify the actual
comparison with b tensor (f mod m) -> b(f mod n).
5. Put d=m/n. The morphism between the Kummer sequences for m and n has components
(d on kernels, d on the middle B, identity on the right B). Since nd=m, its boundary
identity is beta[1] kappa_m = kappa_n by naturality of the short exact triangle.
6. Transpose this equality under both scalar adjunctions and cancel alpha_m, not
kappa_m. It gives b tensor h -> b beta(h), where beta(h)=dh. Thus the shifted
ordinary comparison is precisely the actual transitivity map, with its sign fixed.
7. The quotient tensor is Q_m/nQ_m=F/nF. Local integer lifts and tensor balancing
give the inverse f mod n -> 1 tensor (f mod m). This descends through sheafification
(def-pur-sheaf-tensor-product).
8. The map beta:H_m -> H_n is locally onto: lift t in H_n to z with mz=t and set
h=nz. Its kernel is nH_m: if dh=0, lift h=ny, then my=dh=0. Hence beta induces
H_m/nH_m isomorphic to H_n, the displayed ordinary tensor map. For m=n the maps
are identities; for n=1 the targets vanish. Zero sheaves require no exception. -/
theorem geoCartier_exponent_independence [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : DivisibleReduction.Presentation (J := J) m)
    (Pn : DivisibleReduction.Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) (hF : Pm.S.X₃ = Pn.S.X₃)
    (hH : IsFlatOnSite (R := residues J m) Pm.H)
    (hQ : IsFlatOnSite (R := residues J m) Pm.Q) :
    ∃ (eF : changeOfRings (residueProjection (J := J) h) Pm.Q ≅ Pn.Q)
      (eH : changeOfRings (residueProjection (J := J) h) Pm.H ≅ Pn.H)
      (beta : Pm.H ⟶ (residueRestriction (J := J) h).obj Pn.H),
      (∀ (U : Cᵒᵖ) (f : Pm.S.X₃.val.obj U) (b : (residues J n).obj.obj U),
        eF.hom.val.app U (SuccessiveDerivedQuotient.pure
          (residueProjection (J := J) h) Pm.Q U b (Pm.p.val.app U f)) =
        b • @id (Pn.Q.val.obj U) (Pn.p.val.app U ((eqToHom hF).val.app U f))) ∧
      (∀ (U : Cᵒᵖ) (x : Pm.H.val.obj U),
        Pn.i.val.app U (beta.val.app U x) =
          (m / n) • (eqToHom hB).val.app U (Pm.i.val.app U x)) ∧
      (∀ (U : Cᵒᵖ) (x : Pm.H.val.obj U) (b : (residues J n).obj.obj U),
        eH.hom.val.app U (SuccessiveDerivedQuotient.pure
          (residueProjection (J := J) h) Pm.H U b x) =
          b • @id (Pn.H.val.obj U) (beta.val.app U x)) ∧
      Dmn.T.map (identifications m Dm hm Pm).alphaF.inv ≫
        (transitivity h Dm Dn Dmn).hom.app
          ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₃) ≫
        Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hF)) ≫
        (identifications n Dn hn Pn).alphaF.hom =
      ordinarySingle h Dmn Pm.Q ≫
        (DerivedCategory.singleFunctor (Residue J n) 0).map eF.hom ∧
      Dmn.T.map (identifications m Dm hm Pm).alphaB.inv ≫
        (transitivity h Dm Dn Dmn).hom.app
          ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₁) ≫
        Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hB)) ≫
        (identifications n Dn hn Pn).alphaB.hom =
      (Dmn.T.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Residue J m) 0).obj Pm.H) ≫
        (ordinarySingle h Dmn Pm.H)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor (Residue J n) 0).map eH.hom)⟦(1 : ℤ)⟧' := by
  sorry

end SheafOfModules.GeoCartierExponent
