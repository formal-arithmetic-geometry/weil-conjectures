# AlgebraicGeometry.KummerLine geometry definitions

## Reason

Move the seven existing geometry definitions to `Sheaf.AlgebraicGeometry.KummerLineGeometry`
so the root-coefficient theorem can state its conclusion using them without importing the parent
computation. This is a relocation with identical names, signatures and bodies. The parent publicly
imports the new module, preserving its exported interface. No target meaning changes.
The root and parent proofs use a local irreducibility attribute for `generator` and explicit sheaf arguments
to prevent expensive unfolding; it explicitly unfolds `generator` where its equation is needed.

## Old

In `Sheaf.AlgebraicGeometry.KummerAffineLine`:

```lean
/-- The two affine schemes in the computation.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def curve (k : Type u) [Field k] : Bool → Scheme.{u}
  | false => Spec (CommRingCat.of (Polynomial k))
  | true => Spec (CommRingCat.of (LaurentPolynomial k))

/-- The structure morphisms of the two lines over k.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def structureMap (k : Type u) [Field k] : (b : Bool) → curve k b ⟶ Spec (CommRingCat.of k)
  | false => Spec.map (CommRingCat.ofHom Polynomial.C)
  | true => Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- The canonical open inclusion, induced by k[t] → k[t,t⁻¹].
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def inclusion (k : Type u) [Field k] : curve k true ⟶ curve k false :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

/-- Pullback of a scalar to global functions on either line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def scalar (k : Type u) [Field k] (b : Bool) : k →+* Γ(curve k b, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMap k b).appTop).hom

/-- The global unit t on the punctured line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def coordinateUnit (k : Type u) [Field k] : Γ(curve k true, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom.toMonoidHom
    (LaurentPolynomial.isUnit_T (R := k) 1).unit

/-- The Kummer generator is the actual connecting homomorphism applied to t.
Source: blueprint sk-prop-a1-kummer, Degrees 0 and 1
(blueprint: thm-pur-kummer-affine-line). -/
def generator (k : Type u) [Field k] (m : ℕ) (hm : IsUnit (m : Γ(curve k true, ⊤))) :
    Sheaf.H ((curve k true).rootsOfUnitySheaf m) 1 :=
  (curve k true).kummerδ₀ m hm (Additive.ofMul (coordinateUnit k))

/-- Restriction on root-sheaf cohomology, using the canonical pullback comparison.
Source: Stacks, Tag 03PK (blueprint: thm-pur-kummer-affine-line). -/
def rootRestriction (k : Type u) [Field k] (m q : ℕ) :
    Sheaf.H ((curve k false).rootsOfUnitySheaf m) q →+
      Sheaf.H ((curve k true).rootsOfUnitySheaf m) q :=
  (Sheaf.H.map (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m (inclusion k)) q).comp
    (Etale.cohomologyMap (inclusion k) ((curve k false).rootsOfUnitySheaf m) q)
```

## New

In `Sheaf.AlgebraicGeometry.KummerLineGeometry`, publicly imported by the old module:

```lean
/-- The two affine schemes in the computation.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def curve (k : Type u) [Field k] : Bool → Scheme.{u}
  | false => Spec (CommRingCat.of (Polynomial k))
  | true => Spec (CommRingCat.of (LaurentPolynomial k))

/-- The structure morphisms of the two lines over k.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def structureMap (k : Type u) [Field k] : (b : Bool) → curve k b ⟶ Spec (CommRingCat.of k)
  | false => Spec.map (CommRingCat.ofHom Polynomial.C)
  | true => Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- The canonical open inclusion, induced by k[t] → k[t,t⁻¹].
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def inclusion (k : Type u) [Field k] : curve k true ⟶ curve k false :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

/-- Pullback of a scalar to global functions on either line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def scalar (k : Type u) [Field k] (b : Bool) : k →+* Γ(curve k b, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMap k b).appTop).hom

/-- The global unit t on the punctured line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def coordinateUnit (k : Type u) [Field k] : Γ(curve k true, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom.toMonoidHom
    (LaurentPolynomial.isUnit_T (R := k) 1).unit

/-- The Kummer generator is the actual connecting homomorphism applied to t.
Source: blueprint sk-prop-a1-kummer, Degrees 0 and 1
(blueprint: thm-pur-kummer-affine-line). -/
def generator (k : Type u) [Field k] (m : ℕ) (hm : IsUnit (m : Γ(curve k true, ⊤))) :
    Sheaf.H ((curve k true).rootsOfUnitySheaf m) 1 :=
  (curve k true).kummerδ₀ m hm (Additive.ofMul (coordinateUnit k))

/-- Restriction on root-sheaf cohomology, using the canonical pullback comparison.
Source: Stacks, Tag 03PK (blueprint: thm-pur-kummer-affine-line). -/
def rootRestriction (k : Type u) [Field k] (m q : ℕ) :
    Sheaf.H ((curve k false).rootsOfUnitySheaf m) q →+
      Sheaf.H ((curve k true).rootsOfUnitySheaf m) q :=
  (Sheaf.H.map (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m (inclusion k)) q).comp
    (Etale.cohomologyMap (inclusion k) ((curve k false).rootsOfUnitySheaf m) q)
```

The theorem signature's degree-zero evaluation is annotated explicitly to prevent expensive
inference. Old: `Sheaf.H.equiv₀ _ (MorphismProperty.Over.mkIdTerminal @Etale (curve k b))`.
New: `Sheaf.H.equiv₀ ((curve k b).rootsOfUnitySheaf (ℓ ^ N))
(MorphismProperty.Over.mkIdTerminal @Etale (curve k b))`.
This fills exactly the previously inferred argument; the proposition and all binders are identical.

## Users

The downstream scan found 186 transitive importers. The following are all textual declaration
users reported by `tools/downstream.py --uses curve structureMap inclusion scalar coordinateUnit
generator rootRestriction`; common words produce false positives. Their declarations and
imports require no edits. The old module still exports every name.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KummerAffineLine | Q4 | Definitions relocated; imports geometry publicly. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same names, types and bodies remain available through the public import; no adaptation. |

## Status

landed 20261020T131146-L-1251365 2026-10-20 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.KummerAffineLine)
