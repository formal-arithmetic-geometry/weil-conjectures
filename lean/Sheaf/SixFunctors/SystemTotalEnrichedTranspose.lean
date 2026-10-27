/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X5
-/
module

public import Sheaf.SixFunctors.FiniteAdjunctionDiagramData

/-! # Total-limit transposition of the specified system enriched adjunction

The representation below uses the actual enriched reduction/limit comparison and
actual reconstruction counit. No finite projection determines a morphism here.
Source: steps 2--4 of lem-coef-integral-exceptional-descended-counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralExceptionalMapping
open FiniteAdjunctionDiagram

/-- Represent an actual system morphism in the total mapping complex by applying
limit, the specified gamma, and inverse reconstruction in the first variable.
Source: reconstruction comparison in steps 2--4 of the descended-counit proof
(blueprint: lem-coef-system-total-enriched-transpose). -/
def totalHom {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {W : Scheme.{u}}
    (S : CoefficientDerivedSystemCalculus l E W)
    (P N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N)
    [IsIso (S.adjunction.counit.app P)] (b : P ⟶ N) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).obj
      (coefficientMappingLimit.{u+1}.obj
        ((coefficientSequenceGlobalHom l E W).obj (op P, N))) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
    ((S.gamma l E W ((coefficientSequenceLimit l E W).obj P) N hN).hom ≫
      coefficientMappingLimit.{u+1}.map
        ((coefficientSequenceGlobalHom l E W).map
          (Prod.mkHom (inv (S.adjunction.counit.app P)).op (𝟙 N))))
    ((coefficientIntegralHomEquiv l E W _ _).symm
      ((coefficientSequenceLimit l E W).map b))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SZ : CoefficientDerivedSystemCalculus l E c.Z)
  (SY : CoefficientDerivedSystemCalculus l E Y)
  (r : Realization l E D hl f c SX SZ SY)

variable {l E D hl f c SX SZ SY}

/-- The specified enriched system adjunction sends the total class of b to the
class of its actual system adjunct. This concerns arbitrary normalized finite-Tor
systems, before any restriction to integral constructible objects.

Source: steps 2--4 of lem-coef-integral-exceptional-descended-counit, especially
step 3's enriched counit-transpose identity
(blueprint: lem-coef-system-total-enriched-transpose).

Proof: resolve the strict systems simultaneously by K-flat sources and K-injective
targets. The global enriched transformation is derived sections of the inverse
internal tensor-Hom transpose, by Enriched.component. Uncurrying identifies its
value on a representative b with the system unit followed by G(b), equivalently
the unique arrow whose inverse transpose is F(a) followed by the system counit.
The proper/open projection formula and geometric counit in enrichedMap give this
identity on the actual resolution complexes. Naturality of gamma and the actual
reconstruction counits identifies their total classes with totalHom. Apply total
limit and degree-zero homology to this identity. Localization and independence
of resolutions give the displayed formula for every derived arrow. No equality
is inferred from finite evaluations. The reconstruction triangles also cover
identity morphisms, zero objects and empty schemes. -/
theorem systemTotalEnrichedTranspose
    (CX : CoefficientDerivedSystemCoherence l E X SX)
    (CY : CoefficientDerivedSystemCoherence l E Y SY)
    (g : Geometry l E f SX SY) (s : SectionsPush g)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (a : Enriched r g s βX βY)
    (P : (domain l E X).FullSubcategory) (Q : (domain l E Y).FullSubcategory)
    [IsIso (SY.adjunction.counit.app (r.F.obj P).obj)]
    [IsIso (SX.adjunction.counit.app P.obj)] (b : r.F.obj P ⟶ Q) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
      (coefficientMappingLimit.{u+1}.map (a.iso.hom.app (op P, Q)))
        (totalHom SY (r.F.obj P).obj Q.obj Q.property.1 b.hom) =
      totalHom SX P.obj (r.G.obj Q).obj (r.G.obj Q).property.1
        (r.adjunction.homEquiv P Q b).hom := by
  sorry

end WeilConjectures.IntegralExceptionalMapping
