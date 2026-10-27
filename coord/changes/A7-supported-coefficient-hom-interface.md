# AlgebraicGeometry.SupportedRootScalar coefficient-Hom interface

## Reason

The supported root comparison needs a coefficient-Hom naturality lemma independently of
the root line and scalar endpoints. The generic support and coefficient constructions now
live in its module. The item publicly imports that module, preserving all existing names,
signatures and visibility. The new theorem is a strict part of the argument: it does
not construct root endpoints or supported scalar-extension isomorphisms, identify scalar
arrows, prove uniqueness of coefficient images, or prove the local root-tensor formula.
No target statement or mathematical object changes.

## Old

The following declarations were in `Sheaf.Paper.SupportedRootScalarSiteComparison`:

```lean
/-- The existing etale supported-Hom pair with an arbitrary fixed coefficient ring.
Source: Milne, Section 9, Example 9.5, and the scalar-extension paragraph of
lem-amb-cartier-kummer-map.proof.md.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
abbrev rootScalarSupportPair (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] : SupportHomPair A where
  Site := T.Etale
  topology := T.smallEtaleTopology
  terminal := Scheme.Etale.mk (𝟙 T)
  isTerminal := MorphismProperty.Over.mkIdTerminal _ _
  complement := Scheme.Etale.mk i.openComplement.ι
  restriction := Etale.supportRestrictionArrow i
  supported := Etale.supportedConstantModule (A := A) i
  constantRestriction := Etale.supportedHomConstantRestriction A i

namespace SupportedRootScalar

/-- Degree-zero bounded-below witness; this is used before any site comparison.
Source: blueprint scalar-extension paragraph; Stacks 099R.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def singlePlus {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) : DerivedCategory.Plus C :=
  ⟨SheafExactDegreeZero.obj C M,
    (SheafExactDegreeZero.obj_eq M).symm ▸
      ((DerivedCategory.Plus.singleFunctor C 0).obj M).property⟩

section CoefficientSupport

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
variable {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
variable [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
variable [HasSheafify J A] [HasSheafify J B] [J.HasSheafCompose F]
variable {V W : C} (j : W ⟶ V)

/-- The actual kernel comparison for changing the coefficient category.
It is induced by preservation of kernels, not by any choice of a support map.
Source: Stacks 03FD and 093X; Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def kernelComparison :
    Sheaf.supportedSectionsFunctor J A j ⋙ F ⟶
      sheafCompose J F ⋙ Sheaf.supportedSectionsFunctor J B j where
  app M := CategoryTheory.Limits.kernelComparison (M.obj.map j.op) F
  naturality {M N} f :=
    (kernelComparison_comp_kernel_map (M.obj.map j.op) F (N.obj.map j.op)
      (f.hom.app (op V)) (f.hom.app (op W)) (f.hom.naturality j.op)).symm

variable [dA : HasDerivedCategory.{u + 1} A] [dB : HasDerivedCategory.{u + 1} B]
variable [dSA : HasDerivedCategory.{u + 1} (Sheaf J A)]
variable [dSB : HasDerivedCategory.{u + 1} (Sheaf J B)]
variable [EnoughInjectives (Sheaf J A)] [EnoughInjectives (Sheaf J B)]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [(sheafCompose J F).Additive]
variable [PreservesFiniteLimits (sheafCompose J F)]
variable [PreservesFiniteColimits (sheafCompose J F)]

/-- The canonical derived coefficient comparison on the full supported object.
Its underived transformation is the preceding kernel comparison. In particular no
injectivity of a restricted injective resolution is assumed.
Source: Stacks 03FD and 093X; Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def derivedCoefficientComparison :
    (Sheaf.supportedSectionsFunctor J A j).rightDerivedFunctorPlus ⋙
        F.mapDerivedCategoryPlus ⟶
      (sheafCompose J F).mapDerivedCategoryPlus ⋙
        (Sheaf.supportedSectionsFunctor J B j).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (kernelComparison J F j)

/-- The induced map on supported groups, including the exact-functor homology comparison.
Source: Stacks 03FD and 093X; Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def coefficientGroupMap (K : DerivedCategory.Plus (Sheaf J A)) (a : ℤ) :
    F.obj ((Sheaf.supportHypercohomologyFunctor.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
        J A j a).obj K) ⟶
      (Sheaf.supportHypercohomologyFunctor.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
        J B j a).obj
        ((sheafCompose J F).mapDerivedCategoryPlus.obj K) :=
  (F.mapDerivedCategoryPlusHomologyFunctorIso a).hom.app
      ((Sheaf.supportedSectionsFunctor J A j).rightDerivedFunctorPlus.obj K) ≫
    (DerivedCategory.Plus.homologyFunctor.{u + 1, u + 2, u + 1} B a).map
      ((derivedCoefficientComparison J F j).app K)

end CoefficientSupport

/-- The actual Hom space with its ordinary derived-category hom universe fixed.
This is a type alias, not a new Hom construction. Source: Milne, Section 9, Example 9.5.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
abbrev zeroHom {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A)) : Type (u + 1) :=
  SheafExactDegreeZero.obj _ S.supported ⟶ (SheafExactDegreeZero.obj _ M)⟦(2 : ℤ)⟧

/-- Transport a single-source arrow to the named degree-zero presentation.
Source: the canonical degree-zero comparison in Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
@[irreducible] def fromSingle {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) (K : DerivedCategory C)
    (f : (DerivedCategory.singleFunctor C 0).obj M ⟶ K) :
    SheafExactDegreeZero.obj C M ⟶ K :=
  eqToHom (SheafExactDegreeZero.obj_eq M) ≫ f

/-- Transport a named degree-zero source back to the canonical single source.
Source: the canonical degree-zero comparison in Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
@[irreducible] def toSingle {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) (K : DerivedCategory C)
    (f : SheafExactDegreeZero.obj C M ⟶ K) :
    (DerivedCategory.singleFunctor C 0).obj M ⟶ K :=
  eqToHom (SheafExactDegreeZero.obj_eq M).symm ≫ f

/-- Express the normalized supported-Hom realization using the named degree-zero objects.
Source: Milne, Section 9, evaluation at one and the signed support cone.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def realize {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (chi : S.Identification) (M : Sheaf S.topology (ModuleCat.{u + 1} A))
    (beta : S.group (singlePlus M) 2) :
    zeroHom S M :=
  @fromSingle _ _ _
    (@HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      _ _ _ S.grothendieck) S.supported
        ((SheafExactDegreeZero.obj _ M)⟦(2 : ℤ)⟧) (chi.chi (singlePlus M) 2 beta)

/-- The inverse change of the same single-object presentation.
Source: the ordinary module derived-category convention; no class or lift is chosen.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def homFromZero {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A))
    (b : zeroHom S M) : S.derivedHom (singlePlus M) 2 :=
  @toSingle _ _ _
    (@HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      _ _ _ S.grothendieck) S.supported
        ((SheafExactDegreeZero.obj _ M)⟦(2 : ℤ)⟧) b

/-- Agreement of an evaluation-normalized identification with the signed relative cone.
This uses the existing cone-agreement predicate, rather than changing its boundary sign.
Source: Milne, Section 9; blueprint lem-pur-divisor-relative-cone.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def SignedIdentification {A : Type (u + 1)} [CommRing A]
    (S : SupportHomPair A) (chi : S.Identification) : Prop :=
  ∃ N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction
      S.supported S.constantRestriction,
    N.chi = chi.chi ∧ N.ConeAgreement

```

## New

The generic declarations move to `Sheaf.Paper.SupportedCoefficientHomNaturality`.
The original module publicly imports that module, preserving the existing names and
public interfaces. `singlePlus` constructs the same degree-zero object and proves
bounded-below membership by unfolding the object alias rather than transporting the
property across an equality. Its object is unchanged, and its membership proof is
irrelevant. `singlePlus_obj` records its underlying object. `homPresentation` proves
that the original Hom alias equals the support pair's single-source Hom type, using
the published object equalities. `realizationEquiv` composes the existing identification
with the cast along that equality. `realize` uses its forward cast and `homFromZero` uses the
inverse cast. These are the same canonical degree-zero transports. `presentationEquiv`
also packages the ordinary source equality independently. `homFromZero_realize`
is the proved inverse law in this interface. `realizationEquiv_apply` is its
forward-map equation, used explicitly by uniqueness.

The new module additionally states the coefficient-Hom naturality theorem recorded by
`lem-pur-supported-coefficient-hom-naturality`. This is a decomposition, with one hole
closed and one new hole retained, not a net hole closure.

## Users

`tools/downstream.py Sheaf.Paper.SupportedRootScalarSiteComparison` reports zero current
Lean importers. The unfinished parent DAG route is preserved; the item is not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SupportedRootScalarSiteComparison | A7 | All original declarations and statement preserved through the public import; proof uses the generic coefficient theorem. |

## Status

landed 20261025T163537-L-692667 2026-10-25 (merge of deliver/A7/Sheaf.Paper.SupportedRootScalarSiteComparison)
