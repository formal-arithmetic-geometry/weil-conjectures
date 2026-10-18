/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality

import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
import Sheaf.Paper.RingedTopoiTensorComparisonData
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair

/-!
# Normalized tensor comparison for pro-etale inverse image

Source: Stacks Project, Tags 03EK, 03EL and 09A5
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SheafOfModules

namespace AlgebraicGeometry.ProEtaleTensorComparison

/-- The original small pro-etale ring sheaves, without changing either site universe.
Source: Stacks, Tag 09A5 (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
abbrev Rings (X : Scheme.{u}) := Sheaf (ProEt.topology X) CommRingCat.{u + 1}

/-- The recorded category of modules over the underlying ring sheaf.
Source: Stacks, Section 03EK (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
abbrev Modules {X : Scheme.{u}} (R : Rings X) :=
  ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The recorded inverse-image ring, computed by Kan extension and sheafification.
Source: Stacks, Tags 09A5 and 03D2
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev inverseRing {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) : Rings X :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R

/-- The recorded inverse image on module sheaves; no new module data are chosen.
Source: Stacks, Tag 03D2 (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev inverse {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) :=
  proEtaleModuleInverseImage f R

/-- The recorded sheafification of the sectionwise tensor product.
Source: Stacks, Section 03EK (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev tensor {X : Scheme.{u}} {R : Rings X} (M N : Modules R) : Modules R :=
  (siteSheafTensorRight N).obj M

/-- The local pure tensor followed by the existing sheafification unit.
Source: Stacks, Section 03EK (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev pure {X : Scheme.{u}} {R : Rings X} (M N : Modules R)
    (V : X.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :=
  siteSheafTensorTmul M N (op V) s t

/-- The actual adjunction-unit image of a module section. The small model is used only
inside the already recorded construction; evaluation returns to the original small site.
Source: Stacks, Tags 00VE and 03D2
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def inverseSection {X Y : Scheme.{u}} (f : X ⟶ Y) {R : Rings Y}
    (M : Modules R) (V : Y.ProEt) (s : M.val.obj (op V)) :
    ((inverse f R).obj M).val.obj (op ((proEtaleBaseChange f).obj V)) :=
  (((pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
        (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V))) s

/-- The canonical ring compositor is the adjoint conjugate of pullback associativity.
Source: Stacks, Tag 03CB (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def ringComp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) : inverseRing (g ≫ h) R ≅ inverseRing g (inverseRing h R) :=
  ((conjugateIsoEquiv
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction g CommRingCat.{u + 1}))
    (proEtaleSheafAdjunction (g ≫ h) CommRingCat.{u + 1})).symm
      (AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} g h)).app R


/-- Restriction of scalars is Mathlib's existing functor.
Source: Stacks, Section 03EK (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev restrict {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S) :
    Modules S ⥤ Modules R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)

/-- Inverse image on ring morphisms, from the recorded functor.
Source: Stacks, Tag 03D2 (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev inverseRingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a

/-- The coefficient quotient is uniquely fixed by local pure tensors.
Source: Stacks, Section 03EK; clause 2
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof: the pure pairing over S is R-balanced through a. Its sectionwise bilinear
universal property, followed by module sheafification, gives the stated map. Every
map with the formula has the same adjunct from the tensor presheaf, proving uniqueness. -/
theorem coefficientQuotient_exists {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S)
    (M N : Modules S) :
    ∃! p : tensor ((restrict a).obj M) ((restrict a).obj N) ⟶
        (restrict a).obj (tensor M N),
      ∀ (V : X.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)),
        p.val.app (op V) (pure ((restrict a).obj M) ((restrict a).obj N) V s t) =
          pure M N V s t := by
  sorry

/-- The canonical map from the tensor over R to the tensor over S, selected from its
unique universal-property characterization, rather than from mere existence.
Source: Stacks, Section 03EK (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def coefficientQuotient {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S)
    (M N : Modules S) :
    tensor ((restrict a).obj M) ((restrict a).obj N) ⟶ (restrict a).obj (tensor M N) :=
  Classical.choose (coefficientQuotient_exists a M N)

/-- Inverse image commutes with restriction of the scalar action through a ring map;
the identification is uniquely normalized by the actual adjunction units.
Source: Stacks, Tag 03D2; the scalar identification in clause 2
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof: both objects apply the finite-product-preserving set inverse image to the same
underlying abelian sheaf and action. Naturality with the ring map identifies the actions.
The underlying identity gives the isomorphism and the formula. Taking adjoints shows
that a second map with this formula is equal to it. -/
theorem scalarIdentification_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) (M : Modules S) :
    ∃! e : (inverse f R).obj ((restrict a).obj M) ≅
        (restrict (inverseRingMap f a)).obj ((inverse f S).obj M),
      ∀ (V : Y.ProEt) (s : M.val.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f ((restrict a).obj M) V s) = inverseSection f M V s := by
  sorry

/-- The unit-normalized scalar identification; uniqueness determines its data.
Source: Stacks, Tag 03D2 (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def scalarIdentification {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) (M : Modules S) :
    (inverse f R).obj ((restrict a).obj M) ≅
      (restrict (inverseRingMap f a)).obj ((inverse f S).obj M) :=
  Classical.choose (scalarIdentification_exists f a M)

/-- Existence and uniqueness of the module tensor comparison with its local normalization.
Source: Stacks, Tag 03EL; clause 1
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof:
1. Use the algebraic inverse-image presentation of def-weil-proetale-inverse-image.
Apply lem-weil-pbc-canonical-ringed-tensor-comparison-construction at the identity map
of the inverse-image ring. It gives the normalized scalar-extension tensor comparison.
2. Multiplication gives RI tensor_RI I(M) isomorphic to I(M), inverse m mapped to 1 tensor m.
Conjugate the comparison by these identifications. Its generalized pure-tensor equation,
evaluated on the pair of unit images of s and t, gives the displayed local formula.
3. For uniqueness, take the module-adjunction adjuncts of two proposed maps. These are
R-linear and agree on every original pure tensor by the formula. The injectivity of the
Hom-to-bilinear-map correspondence in lem-pc-sites-sheaf-tensor-bilinear-universal makes
the adjuncts equal; injectivity of the adjunction then makes the maps equal. This does
not assert that the original pulled-back pure tensors generate locally on the target. -/
theorem comparison_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y)
    (M N : Modules R) :
    ∃! s : (inverse f R).obj (tensor M N) ⟶
        tensor ((inverse f R).obj M) ((inverse f R).obj N),
      ∀ (V : Y.ProEt) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
        s.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (tensor M N) V (pure M N V x y)) =
        pure ((inverse f R).obj M) ((inverse f R).obj N)
          ((proEtaleBaseChange f).obj V) (inverseSection f M V x) (inverseSection f N V y) := by
  sorry

/-- The canonical sigma, determined uniquely by its local pure-tensor formula.
Source: Stacks, Tag 03EL (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y)
    (M N : Modules R) :
    (inverse f R).obj (tensor M N) ⟶ tensor ((inverse f R).obj M) ((inverse f R).obj N) :=
  Classical.choose (comparison_exists f R M N)

/-- The tensor map in both variables is the composite of the two recorded factor maps.
Source: Stacks, Section 03EK (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def tensorMap {X : Scheme.{u}} {R : Rings X} {M M' N N' : Modules R}
    (a : M ⟶ M') (b : N ⟶ N') : tensor M N ⟶ tensor M' N' :=
  (siteSheafTensorRight N).map a ≫ siteSheafTensorSecondMap M' b


/-- The underlying set sheaf of a commutative ring sheaf.
Source: Stacks, Tag 00YV (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev ringSets {X : Scheme.{u}} (R : Rings X) :=
  (sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R

/-- The underlying set sheaf of a module sheaf, using the existing forgetful functors.
Source: Stacks, Tag 03D2 (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev moduleSets {X : Scheme.{u}} {R : Rings X} (M : Modules R) :=
  ((toSheaf _ ⋙ sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M)

/-- The underlying-set identification of ring inverse image is uniquely unit-normalized.
Source: Stacks, Tag 00YV; the operation transport in clause 3
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof: lift the finite-product-preserving set inverse image to commutative ring objects.
The original operation maps give the ring identities after applying this functor.
The lifted adjunction identifies the ring unit with the set unit. Uniqueness follows
by taking adjuncts: the displayed formula identifies the adjunct with the ring unit
on every object and every section. -/
theorem ringSetsIdentification_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) :
    ∃! e : (AlgebraicGeometry.ProEtale.setPullback f).obj (ringSets R) ≅
        ringSets (inverseRing f R),
      ∀ (V : Y.ProEt) (r : R.obj.obj (op V)),
        e.hom.hom.app (op ((proEtaleBaseChange f).obj V))
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
            (ringSets R)).hom.app (op V) r) =
        ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r := by
  sorry

/-- The determined underlying-set identification for inverse-image rings.
Source: Stacks, Tag 00YV (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def ringSetsIdentification {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) :
    (AlgebraicGeometry.ProEtale.setPullback f).obj (ringSets R) ≅
      ringSets (inverseRing f R) :=
  Classical.choose (ringSetsIdentification_exists f R)

/-- The underlying-set identification of module inverse image is uniquely unit-normalized.
Source: Stacks, Tag 03D2; the operation transport in clause 3
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof: addition and the scalar action are transported through finite-product comparisons.
They define the same module inverse image as the recorded small-model construction.
Its adjunction identifies its unit with the set unit. Any second identification has the
same adjunct on every section, and hence is equal by the set-sheaf adjunction. -/
theorem moduleSetsIdentification_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) :
    ∃! e : (AlgebraicGeometry.ProEtale.setPullback f).obj (moduleSets M) ≅
        moduleSets ((inverse f R).obj M),
      ∀ (V : Y.ProEt) (s : M.val.obj (op V)),
        e.hom.hom.app (op ((proEtaleBaseChange f).obj V))
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
            (moduleSets M)).hom.app (op V) s) = inverseSection f M V s := by
  sorry

/-- The determined underlying-set identification for inverse-image modules.
Source: Stacks, Tag 03D2 (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def moduleSetsIdentification {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) :
    (AlgebraicGeometry.ProEtale.setPullback f).obj (moduleSets M) ≅
      moduleSets ((inverse f R).obj M) :=
  Classical.choose (moduleSetsIdentification_exists f M)

/-- The module compositor is uniquely fixed by the images of original sections,
with the canonical fibre-product associator written explicitly.
Source: Stacks, Tags 03CB and 03D2; clause 3
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof: the adjunction-normalized set compositor is compatible with projections to each
factor of every product. Naturality with the addition and scalar-action maps makes it
semilinear over the ring compositor. Thus it induces the displayed module isomorphism.
Its unit equation gives the formula. If another isomorphism has the formula, taking
adjuncts identifies it on all sections, giving uniqueness. -/
theorem moduleComp_exists {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (M : Modules R) :
    ∃! e : (inverse (g ≫ h) R).obj M ≅
        (restrict (ringComp g h R).hom).obj
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj M)),
      ∀ (V : Z.ProEt) (s : M.val.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
          (inverseSection (g ≫ h) M V s) =
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
            (inverseSection h M V s)) := by
  sorry

/-- The canonical semilinear module compositor, from its unique unit characterization.
Source: Stacks, Tags 03CB and 03D2
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def moduleComp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (M : Modules R) :
    (inverse (g ≫ h) R).obj M ≅
      (restrict (ringComp g h R).hom).obj
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M)) :=
  Classical.choose (moduleComp_exists g h R M)

/-- The canonical ring identity comparison, from the inverse-image adjunction.
Source: Stacks, Tag 00VE (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def ringId {X : Scheme.{u}} (R : Rings X) : inverseRing (𝟙 X) R ≅ R :=
  ((conjugateIsoEquiv Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).symm).app R

/-- The module identity comparison is uniquely normalized by the identity unit.
Source: Stacks, Tags 00VE and 03D2; the last sentence of clause 3
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof: the comma category at U has initial object (U,id), terminal in the opposite
colimit index. The colimit is M(U), compatibly with restrictions. Since M is a sheaf,
sheafification changes nothing. The same holds for R and its action, giving the stated
semilinear isomorphism. The adjunction makes any other normalized isomorphism equal. -/
theorem moduleId_exists {X : Scheme.{u}} (R : Rings X) (M : Modules R) :
    ∃! e : (inverse (𝟙 X) R).obj M ≅ (restrict (ringId R).hom).obj M,
      ∀ (V : X.ProEt) (s : M.val.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (inverseSection (𝟙 X) M V s) =
        M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op s := by
  sorry

/-- The canonical module identity comparison, from its unique unit characterization.
Source: Stacks, Tag 00VE (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable def moduleId {X : Scheme.{u}} (R : Rings X) (M : Modules R) :
    (inverse (𝟙 X) R).obj M ≅ (restrict (ringId R).hom).obj M :=
  Classical.choose (moduleId_exists R M)


/-- Forget a ring morphism to its actual underlying sheaf map.
Source: Stacks, Tag 00YV (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev ringMapSets {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S) :=
  (sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).map a

/-- Forget a module morphism to its actual underlying sheaf map.
Source: Stacks, Tag 03D2 (blueprint: lem-pur-proetale-inverse-image-tensor-comparison). -/
noncomputable abbrev moduleMapSets {X : Scheme.{u}} {R : Rings X}
    {M N : Modules R} (a : M ⟶ N) :=
  (toSheaf _ ⋙ sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).map a

/-- Uniqueness of the set compositor with its sectionwise unit normalization. Equality
of sheaf maps in this formula is equality on all sections of all original site objects.
Source: Stacks, Tags 00VE, 00WX and 03CB; clause 3
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof: conjugation of the canonical direct-image comparison gives setPullbackComp and
its unit equation. If another natural isomorphism has that equation, each of its
components has the same adjunct. Adjunction injectivity identifies the components,
and natural-transformation extensionality identifies the natural isomorphisms. -/
theorem setComp_unique {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (e : AlgebraicGeometry.ProEtale.setPullback (g ≫ h) ≅
      AlgebraicGeometry.ProEtale.setPullback h ⋙ AlgebraicGeometry.ProEtale.setPullback g) :
    (∀ H : Sheaf (ProEt.topology Z) (Type (u + 1)),
      (AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app H ≫
        (AlgebraicGeometry.ProEtale.lowerStar (Type (u + 1)) (g ≫ h)).map (e.hom.app H) =
      ((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).comp
        (AlgebraicGeometry.ProEtale.setPullbackAdjunction g)).unit.app H ≫
        (AlgebraicGeometry.ProEtale.lowerStarComp (Type (u + 1)) g h).hom.app
          ((AlgebraicGeometry.ProEtale.setPullback h ⋙
            AlgebraicGeometry.ProEtale.setPullback g).obj H)) ↔
      e = AlgebraicGeometry.ProEtale.setPullbackComp g h := by
  sorry

/-- The normalized pro-etale inverse-image tensor comparison: invertibility, local formula,
joint naturality, coefficient change, set/ring/module composition, and the identity case.
The existence and uniqueness assertions are comparison_exists and setComp_unique; the
coefficient quotient and the semilinear identifications above have unique normalizations.
Source: Stacks, Tags 03EK, 03EL and 09A5, with Tags 00VE, 00WH, 00WX and 03CB for coherence
(blueprint: lem-pur-proetale-inverse-image-tensor-comparison).
Proof:
1. Apply the canonical normalized ringed tensor construction with scalar map id_RI.
Multiplication RI tensor_RI I(M) to I(M), inverse m mapped to 1 tensor m, conjugates its
isomorphism to comparison. The generalized-element normalization at the pair (s,t),
using naturality of the unit with both projections, is the displayed local formula.
Naturality of the construction gives joint naturality and invertibility.
2. Taking adjuncts identifies two candidate maps if they agree on all original pure
tensors: the module adjunction makes the adjuncts R-linear, and the tensor bilinear
universal property identifies them. This is the uniqueness argument of comparison_exists.
3. The quotient pairings are balanced over the smaller ring. On every pulled-back
original pure tensor, naturality of the unit for the quotient and the normalization of
comparison give the same tensor in the larger-ring tensor product on both routes.
Apply the adjunct equality criterion of step 2 to get the coefficient equation.
4. Conjugate the direct-image pullback-associativity comparison to get the canonical set
compositor. Its adjunction-unit equation gives the section formula and setComp_unique.
The product-projection comparisons commute with this natural isomorphism, and naturality
with every operation map therefore transports ring addition/multiplication and module
addition/action. The terminal-object equation transports zero and one. These are exactly
the ringComp and moduleComp underlying-set equations below.
5. Evaluate the two tensor-composition routes on each original pulled-back pure tensor.
The unit formulas change both to the same iterated inverse images of its two factors.
The criterion of step 2, now for g followed by h, proves the entire morphism equation.
6. At the identity the comma index has initial object (U,id), hence its opposite has a
terminal object. The colimit is the original section object, naturally in U; sheafification
of an existing sheaf changes nothing. Thus the identity unit is an isomorphism. Under it,
comparison sends each pure tensor to itself; tensor universality proves the last equation. -/
theorem inverseImage_tensor_comparison {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (M N : Modules R) :
    IsIso (comparison h R M N) ∧
    (∀ (V : Z.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)),
      (comparison h R M N).val.app (op ((proEtaleBaseChange h).obj V))
        (inverseSection h (tensor M N) V (pure M N V s t)) =
      pure ((inverse h R).obj M) ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
        (inverseSection h M V s) (inverseSection h N V t)) ∧
    (∀ (M' N' : Modules R) (a : M ⟶ M') (b : N ⟶ N'),
      (inverse h R).map (tensorMap a b) ≫ comparison h R M' N' =
        comparison h R M N ≫ tensorMap ((inverse h R).map a) ((inverse h R).map b)) ∧
    (∀ (S : Rings Z) (a : R ⟶ S) (F G : Modules S),
      (inverse h R).map (coefficientQuotient a F G) ≫
          (scalarIdentification h a (tensor F G)).hom ≫
          (restrict (inverseRingMap h a)).map (comparison h S F G) =
        comparison h R ((restrict a).obj F) ((restrict a).obj G) ≫
          tensorMap (scalarIdentification h a F).hom (scalarIdentification h a G).hom ≫
          coefficientQuotient (inverseRingMap h a)
            ((inverse h S).obj F) ((inverse h S).obj G)) ∧
    ((AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app (ringSets R) ≫
        (AlgebraicGeometry.ProEtale.setPullback g).map (ringSetsIdentification h R).hom ≫
        (ringSetsIdentification g (inverseRing h R)).hom =
      (ringSetsIdentification (g ≫ h) R).hom ≫ ringMapSets (ringComp g h R).hom) ∧
    (∀ P : Modules R,
      (AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app (moduleSets P) ≫
          (AlgebraicGeometry.ProEtale.setPullback g).map (moduleSetsIdentification h P).hom ≫
          (moduleSetsIdentification g ((inverse h R).obj P)).hom =
        (moduleSetsIdentification (g ≫ h) P).hom ≫ moduleMapSets (moduleComp g h R P).hom) ∧
    ((moduleComp g h R (tensor M N)).hom ≫
        (restrict (ringComp g h R).hom).map
          ((inverse g (inverseRing h R)).map (comparison h R M N)) ≫
        (restrict (ringComp g h R).hom).map
          (comparison g (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N)) =
      comparison (g ≫ h) R M N ≫
        tensorMap (moduleComp g h R M).hom (moduleComp g h R N).hom ≫
        coefficientQuotient (ringComp g h R).hom
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))) ∧
    (∀ H : Sheaf (ProEt.topology Z) (Type (u + 1)),
      IsIso ((AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 Z)).unit.app H)) ∧
    (comparison (𝟙 Z) R M N ≫ tensorMap (moduleId R M).hom (moduleId R N).hom ≫
      coefficientQuotient (ringId R).hom M N = (moduleId R (tensor M N)).hom) := by
  sorry

end AlgebraicGeometry.ProEtaleTensorComparison
