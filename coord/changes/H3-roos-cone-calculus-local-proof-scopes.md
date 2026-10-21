# Sheaf.Algebra.Homology.RoosConeCalculus

## Reason

Document the local proof environment required by the completed proof. The server's
stage-3 preflight requested this record under gate (d) because added command-level
attributes and scopes cannot be classified as proof-body changes by its static check.

The change is computational and local to this module. No public declaration type,
definition body, visibility, import or persistent attribute is changed. All new helpers
are private and proved. Existing public definitions and the theorem signature are
unchanged byte for byte. No target meaning changes and no consumer adaptation is needed.

The private product, cone and shift constructions are made locally irreducible after
their coordinate APIs are proved, preventing later proofs from unfolding their chosen
limit data. Three private instances are local to Coordinates. Two omit commands avoid
unnecessary countable-product parameters in private helpers. Coordinates now also
contains the private proof and its generic assembly; it closes before the public theorem.
The added backward-defeq option applies only while elaborating this module.

The final local irreducibility commands for roosF and roosConeFunctor and the two scoped
transparency options prevent expansion of the concrete sheaf-module functor while
elaborating the original theorem statement. The scoped options wrap only that theorem.
The namespace ends immediately afterward, so the local attributes do not survive the
module. The complete module compiles without warnings in 33.2 seconds; the unchanged
statement with the former elaboration environment caused repeated 60-second timeouts.
No timeout or heartbeat limit is increased.

An independent reader can check the unchanged public declarations against the source,
the private visibility of the added helpers, the Coordinates/namespace boundaries,
and that every added attribute is local and every new specialization option is scoped.

## Old

Original file-local settings, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Original public theorem signature, verbatim:

```lean
theorem roos_cone_calculus
    (X : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)] :
    (roosF (A := ringedSiteModules.{max u (t + 1)} R)).Additive ∧
    CoordinateCalculus (ringedSiteModules.{max u (t + 1)} R) ∧
    (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
      (f : N ⟶ N'),
      (∀ n : ℕ, QuasiIso
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))) →
      QuasiIso (roosF.map f)) ∧
    (∀ N : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ,
      DerivedRoos N) ∧
    ∃ (cs : (roosF (A := ringedSiteModules.{max u (t + 1)} R)).CommShift ℤ)
      (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
      (hnat : AugmentationNaturality (ringedSiteModules.{max u (t + 1)} R)),
      ShiftFormula cs ∧
      (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), ConeFormula f (e f)) ∧
      ConeCompatibility cs e ∧ ConeAugmentation e hnat ∧ ShiftAugmentation cs
```

## New

Added local/scoped commands, in file order, verbatim:

```lean
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] productLimit productLift
attribute [local irreducible] fibrePair
attribute [local irreducible] conePair
attribute [local irreducible] productTarget productSource
attribute [local irreducible] productPair
attribute [local irreducible] coneInvComponent
attribute [local irreducible] coneHomComponent
attribute [local irreducible] coneComponentIso coneIso
attribute [local instance] levelCommShift
omit [HasCountableProducts A] in
attribute [local instance] productShift
attribute [local irreducible] productShiftComponent
attribute [local irreducible] productShiftComponentAt
attribute [local instance] transitionEndomorphism_shift
omit [HasCountableProducts A] in
attribute [local irreducible] roosShiftMap
attribute [local irreducible] roosCommShift
attribute [local irreducible] roosF roosConeFunctor
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

The public theorem signature is unchanged, verbatim:

```lean
theorem roos_cone_calculus
    (X : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)] :
    (roosF (A := ringedSiteModules.{max u (t + 1)} R)).Additive ∧
    CoordinateCalculus (ringedSiteModules.{max u (t + 1)} R) ∧
    (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
      (f : N ⟶ N'),
      (∀ n : ℕ, QuasiIso
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))) →
      QuasiIso (roosF.map f)) ∧
    (∀ N : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ,
      DerivedRoos N) ∧
    ∃ (cs : (roosF (A := ringedSiteModules.{max u (t + 1)} R)).CommShift ℤ)
      (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
      (hnat : AugmentationNaturality (ringedSiteModules.{max u (t + 1)} R)),
      ShiftFormula cs ∧
      (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), ConeFormula f (e f)) ∧
      ConeCompatibility cs e ∧ ConeAugmentation e hnat ∧ ShiftAugmentation cs
```

The proof now constructs the countable-exact-product instance and applies the proved
private assemble_calculus. There is no remaining sorry and no changed public definition.

## Users

Read-only check performed with tools/downstream.py on the current shared source:
Sheaf.Algebra.Homology.RoosConeCalculus --uses roos_cone_calculus roosF roosConeFunctor.
It reports zero downstream modules. The only textual uses it reports within this
module's import closure are in the item itself (roos_cone_calculus and roosF).
This is an interface check, not a withdrawal argument; the node remains needed by its
unfinished DAG parents and is delivered with its proof.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RoosConeCalculus | H3 | Local proof scopes and private helpers; all existing public signatures, definitions, visibility and public imports unchanged. |

No other module is adapted, and there are no forced adaptations.

## Status

landed 20261021T101122-L-12295 2026-10-21 (merge of deliver/H3/Sheaf.Algebra.Homology.RoosConeCalculus)
