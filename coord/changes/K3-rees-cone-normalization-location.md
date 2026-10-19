# AlgebraicGeometry.Etale.FiniteSmoothPurity.ReesConeNormalized

## Reason

Relocate the normalization definitions below their existence and uniqueness proofs to avoid
an import cycle. Declaration names, types, bodies, visibility and universes are unchanged.
Only their docstrings now cite the definition node recording their new module. No target
statement or definition meaning changes.

## Old

In `Sheaf.Paper.FiniteSmoothCanonicalInterfaces`:

```lean
/-- The conormal algebra identified with functions on its relative spectrum.
Source: Stacks 01LX and 0630
(blueprint: def-pur-finite-smooth-canonical-interfaces). -/
def coneAlgebraIso {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    (PurityNormalBundle.algebraObject s).obj ≅
      Under.mk (⟨(PurityNormalBundle.projection s).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (PurityNormalBundle.projection s).base).obj
            (PurityNormalBundle.normalCone s).sheaf) :=
  ((ObjectProperty.ι (fun B : S.CommAlgebraSheaf ↦ B.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence S).counitIso.app
      (PurityNormalBundle.algebraObject s))).symm ≪≫
    eqToIso ((affine_morphism_relative_spec S).2.choose_spec.choose
      (PurityNormalBundle.over s))

/-- The affine-chart inclusion in the actual Rees zero fibre.
Source: extended-Rees gluing, sk-thm-dnc
(blueprint: def-pur-finite-smooth-canonical-interfaces). -/
def reesConeChart {V S : Scheme.{u}} (s : S ⟶ V) (U : V.AffineZariskiSite) :
    Spec (s.ker.normalConePresheaf.obj (Opposite.op U)) ⟶ s.ker.normalCone :=
  colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
    s.ker.coequifibered_toNormalConePresheaf).functor U

/-- The canonical associated-graded identification fixes constants and sends a degree-one
ideal class of a to a/t modulo t on EVERY affine chart. These classes generate the graded
algebra, so this condition rules out rescaling and all other bundle automorphisms.
Source: Stacks 0630, 0632; sk-thm-dnc, Local construction
(blueprint: def-pur-finite-smooth-canonical-interfaces). -/
def ReesConeNormalized {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s]
    (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s) : Prop :=
  q.hom ≫ PurityNormalBundle.projection s = Scheme.Hom.purityNormalProjection s ∧
  s.normalConeZeroSection ≫ q.hom = PurityNormalBundle.zeroSection s ∧
  ∀ (U : V.AffineZariskiSite)
    (b : (ConormalGradedAlgebra.power s 1).val.obj (Opposite.op U.1))
    (hb : (ConormalGradedAlgebra.powerInclusion s 1).val.app (Opposite.op U.1) b ∈
      s.ker.siteIdeal U)
    (hU : ⊤ ≤ (reesConeChart s U ≫ q.hom) ⁻¹ᵁ
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1))),
    ((reesConeChart s U ≫ q.hom).appLE
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ⊤ hU)
        (((coneAlgebraIso s).hom.right.hom.app (Opposite.op (s ⁻¹ᵁ U.1)))
          (ConormalGradedAlgebra.homogeneousClass s
            (ConormalGradedAlgebra.presentation s).algebra
            (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 b)) =
      (Scheme.ΓSpecIso (s.ker.normalConePresheaf.obj (Opposite.op U))).inv
        (Ideal.Quotient.mk (s.ker.tIdeal (Opposite.op U))
          ⟨LaurentPolynomial.C (R := Γ(V, U.1))
              ((ConormalGradedAlgebra.powerInclusion s 1).val.app (Opposite.op U.1) b) *
            LaurentPolynomial.T (-1),
            Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (I := s.ker.siteIdeal U) hb⟩)
```

## New

The same three definitions are in `Sheaf.AlgebraicGeometry.ReesConeNormalization` and
publicly re-exported from `Sheaf.Paper.FiniteSmoothCanonicalInterfaces`. Their verbatim
signatures and bodies are those in Old; only the blueprint tags name the relocation node.

```lean
/-- The conormal algebra identified with functions on its relative spectrum.
Source: Stacks 01LX and 0630
(blueprint: def-pur-rees-cone-normalization). -/
def coneAlgebraIso {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    (PurityNormalBundle.algebraObject s).obj ≅
      Under.mk (⟨(PurityNormalBundle.projection s).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (PurityNormalBundle.projection s).base).obj
            (PurityNormalBundle.normalCone s).sheaf) :=
  ((ObjectProperty.ι (fun B : S.CommAlgebraSheaf ↦ B.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence S).counitIso.app
      (PurityNormalBundle.algebraObject s))).symm ≪≫
    eqToIso ((affine_morphism_relative_spec S).2.choose_spec.choose
      (PurityNormalBundle.over s))

/-- The affine-chart inclusion in the actual Rees zero fibre.
Source: extended-Rees gluing, sk-thm-dnc
(blueprint: def-pur-rees-cone-normalization). -/
def reesConeChart {V S : Scheme.{u}} (s : S ⟶ V) (U : V.AffineZariskiSite) :
    Spec (s.ker.normalConePresheaf.obj (Opposite.op U)) ⟶ s.ker.normalCone :=
  colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
    s.ker.coequifibered_toNormalConePresheaf).functor U

/-- The canonical associated-graded identification fixes constants and sends a degree-one
ideal class of a to a/t modulo t on EVERY affine chart. These classes generate the graded
algebra, so this condition rules out rescaling and all other bundle automorphisms.
Source: Stacks 0630, 0632; sk-thm-dnc, Local construction
(blueprint: def-pur-rees-cone-normalization). -/
def ReesConeNormalized {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s]
    (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s) : Prop :=
  q.hom ≫ PurityNormalBundle.projection s = Scheme.Hom.purityNormalProjection s ∧
  s.normalConeZeroSection ≫ q.hom = PurityNormalBundle.zeroSection s ∧
  ∀ (U : V.AffineZariskiSite)
    (b : (ConormalGradedAlgebra.power s 1).val.obj (Opposite.op U.1))
    (hb : (ConormalGradedAlgebra.powerInclusion s 1).val.app (Opposite.op U.1) b ∈
      s.ker.siteIdeal U)
    (hU : ⊤ ≤ (reesConeChart s U ≫ q.hom) ⁻¹ᵁ
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1))),
    ((reesConeChart s U ≫ q.hom).appLE
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ⊤ hU)
        (((coneAlgebraIso s).hom.right.hom.app (Opposite.op (s ⁻¹ᵁ U.1)))
          (ConormalGradedAlgebra.homogeneousClass s
            (ConormalGradedAlgebra.presentation s).algebra
            (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 b)) =
      (Scheme.ΓSpecIso (s.ker.normalConePresheaf.obj (Opposite.op U))).inv
        (Ideal.Quotient.mk (s.ker.tIdeal (Opposite.op U))
          ⟨LaurentPolynomial.C (R := Γ(V, U.1))
              ((ConormalGradedAlgebra.powerInclusion s 1).val.app (Opposite.op U.1) b) *
            LaurentPolynomial.T (-1),
            Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (I := s.ker.siteIdeal U) hb⟩)
```

## Users

`tools/downstream.py Sheaf.Paper.FiniteSmoothCanonicalInterfaces --uses <name>` was run
for all three relocated names. It lists the following 27 downstream modules; only the
assigned module itself uses those names directly in the original library. Each consumer
retains the same imported interface through the public re-export. No existing consumer
is edited, including the modules held by other groups.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteSmoothCanonicalInterfaces | K3 | Public re-export of identical definitions. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | Same public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Same declarations publicly re-exported; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same declarations publicly re-exported; no adaptation. |
| TargetsCheck | unclaimed | Same declarations publicly re-exported; no adaptation. |
| WeilConjectures | unclaimed | Same declarations publicly re-exported; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same declarations publicly re-exported; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same declarations publicly re-exported; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same declarations publicly re-exported; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same declarations publicly re-exported; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same declarations publicly re-exported; no adaptation. |
| Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence | new K3 | Imports the definitions below existence. |

The current-source declaration parser confirms identical signatures for all six existing
declarations and identical bodies for all five existing definitions/abbreviations. The
three downstream scans were repeated on resumption and returned 27 consumers, including
seven modules added since the retained attempt. All seven have the same unchanged interface.

The unchanged direct importer `Sheaf.Paper.FiniteSmoothPurityMaps` was compiled against
the delivered overlay in this session: exit 0, no warnings, 6.5 seconds.

## Status

landed 20261019T192801-L-1867479 2026-10-19 (merge of deliver/K3/Sheaf.Paper.FiniteSmoothCanonicalInterfaces)
