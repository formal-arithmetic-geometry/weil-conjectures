## Worker report

The node is already stated by the landed project declaration
`AlgebraicGeometry.ProEtale.proEtale_extension_by_zero` in
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`. I therefore record that declaration as
`existing: true` and add no module or duplicate definition. Its helper declarations are
`geometricModuleStalkFunctor`, `geometricModuleStalkFunctor_additive`,
`openExtensionCochain`, `openExtensionScalarRestriction_additive`, and
`openExtensionScalarMap` in the same module.

The theorem signature renders every node clause verbatim. A finite commutative ring is
`A : Type (u + 1)` with `[CommRing A] [Finite A]`; schemes and the open immersion are
`{U X : Scheme.{u}}`, `j : U ⟶ X`, `[IsOpenImmersion j]`. Exactness is expressed by
`PreservesFiniteLimits` and `PreservesFiniteColimits` of
`openImmersionLowerShriek (ModuleCat.{u + 1} A) j`. The adjunction clause uses the
recorded `openImmersionRestriction`, and the degreewise complex functor is the explicit
`openExtensionCochain A j` abbreviation based on `mapHomologicalComplex (.up ℤ)`.
The inside-point clause quantifies `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and
`y : Spec (.of Ω) ⟶ U`, asserting a `Nonempty` natural isomorphism of the two whole
complex stalk functors. The complement clause uses the same point data on `X`, the
negated factorization condition, and asserts `IsZero` for every source cochain complex.
The scalar clause quantifies every finite commutative `B : Type (u + 1)` and every
`φ : A →+* B`, asserting `IsIso` for the canonical mate `openExtensionScalarMap φ j`
and its termwise complex map.

Dependency declarations read and used are `AlgebraicGeometry.ProEtale.openImmersionLowerShriek`
and its adjunction/restriction declarations from
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`,
`AlgebraicGeometry.Scheme.proEtaleGeometricNeighbourhoodForget` and the geometric
stalk declarations from `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`, and
Mathlib's `SheafOfModules.restrictScalars` for
`def-pc-sheaf-restrict-scalars`. The convention node contributes the existing
`Scheme` and `IsOpenImmersion` notions; the pro-etale-site node contributes
`Scheme.ProEt.topology`.

Edge cases checked include empty `U` and `X`, the identity immersion, the zero
coefficient ring, arbitrary (including noninjective and nonsurjective) coefficient maps,
unbounded and negative complex degrees, and vacuous geometric-point clauses. No extra
nonemptiness, characteristic, finiteness of schemes, or universe equality is present.

Searches used `msearch.py` LeanFinder, Loogle, grep, and LeanSearch, plus `rg` over
Mathlib, `WeilConjectures`, and `lean/Sheaf`. They found ordinary sheaf restriction or
stalk declarations but no complete pro-etale extension-by-zero statement. The exact
landed declaration was then verified with `scompile.py --source
Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`; its theorem signature is identical to
the node's statement. No statement correction, disputed statement, new node, or
dependency-module repair is needed.

## Second reading by N8

I read the node `lem-cbc-proetale-extension-zero` and its source place before checking
 the Lean declaration. The node's objects, hypotheses, and conclusion are rendered as
follows.

1. A finite commutative ring is rendered by `A : Type (u + 1)` with
   `[CommRing A] [Finite A]`. This has the same coefficient hypotheses and retains the
   zero ring case.
2. Schemes and an open immersion are rendered by `{U X : Scheme.{u}}`,
   `j : U ⟶ X`, and `[IsOpenImmersion j]`. No finiteness, separation, nonemptiness, or
   characteristic hypothesis is added.
3. Exactness of extension by zero is rendered by the conjunction of
   `PreservesFiniteLimits (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)` and
   `PreservesFiniteColimits` for the same canonical lower-shriek functor. This is the
   exactness clause of the node.
4. The left-adjoint clause is rendered by
   `Nonempty (openImmersionLowerShriek ... j ⊣ openImmersionRestriction ... j)`, using
   the recorded pro-etale restriction functor and not an etale or private substitute.
5. Degreewise action on cochain complexes is rendered by the canonical abbreviation
   `openExtensionCochain A j`, namely `mapHomologicalComplex (.up ℤ)` of the same
   lower-shriek, together with its adjunction to the mapped restriction functor.
6. For an algebraically closed field `Ω : Type u` and a geometric point
   `y : Spec (.of Ω) ⟶ U`, the declaration gives a `Nonempty` natural isomorphism
   between `openExtensionCochain A j` followed by the stalk functor at `y ≫ j` and
   the stalk functor at `y`, both mapped degreewise. This is the inside-point stalk
   prescription for every complex and is natural in morphisms and differentials.
7. For a geometric point `y : Spec (.of Ω) ⟶ X` with no factorization through `U`,
   the declaration quantifies every cochain complex over `U` and asserts `IsZero` of
   its extension's stalk. This is exactly the complement stalk prescription.
8. For every finite commutative `B : Type (u + 1)` and ring homomorphism
   `φ : A →+* B`, the canonical mate `openExtensionScalarMap φ j` is asserted to be an
   isomorphism, as is its degreewise mapped-complex transformation. Its direction is
   `j_!^A Res → Res j_!^B`; taking the inverse gives the node's displayed canonical
   isomorphism `Res j_!^B ≅ j_!^A Res`.

The declaration is the landed project declaration
`AlgebraicGeometry.ProEtale.proEtale_extension_by_zero` in
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`; its signature is verbatim the node
copy. The helper declarations in that module are canonical constructions used by the
signature: the geometric module stalk functor, the degreewise cochain functor, the
additivity instance for scalar restriction, and the scalar mate. No duplicate
definition or dependency repair is needed.

I checked edge cases explicitly: empty `U` or `X` and the identity immersion are
allowed; the zero coefficient ring is allowed by `[CommRing A] [Finite A]`; coefficient
maps may be noninjective or nonsurjective; complexes are unbounded and include negative
degrees; and the point clauses are correctly vacuous when their point or factorization
condition has no instance. The site object and point universes are both `u`, while the
module universe is `u + 1`, so no universe equality or case is silently excluded.

For duplicate searches I ran `msearch.py` LeanFinder, Loogle, and grep searches and
searched the project and Mathlib sources. The searches found only general stalk,
sheafification, and adjunction declarations; no complete pro-etale extension-by-zero
statement. I also opened the exact source module and checked the declaration with
`scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`. The Stacks source
places agree: Tags 03DI and 03DJ supply the module adjunction and exactness, while Tag
09AE defines pro-etale extension by zero. No mismatch was found, so no Lean or node
repair, statement correction, disputed marker, citer audit, or new node was required.
