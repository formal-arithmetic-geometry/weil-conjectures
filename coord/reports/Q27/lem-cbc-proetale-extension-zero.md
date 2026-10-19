## Worker report

This is an existing-declaration delivery. The item was already stated and reviewed by NR.
Reuse `AlgebraicGeometry.ProEtale.proEtale_extension_by_zero` in
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero` (line 131), without writing, replacing,
or recompiling a duplicate source module. Read the full published module and confirmed
its current server source with `scompile.py --source`. Only the item's `lean` record
changes; its statement, dependencies, and all other fields are preserved. The theorem
still has the expected stage-2 `sorry` proof. No new nodes or dependency repairs are needed.

Hypothesis and clause correspondence:

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
- The schemes and open immersion are `{U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j]`. There are no extra separation, compactness, or finiteness
  hypotheses on either scheme or on the immersion.
- The small pro-etale sheaf category is
  `Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)`, with the corresponding
  category on X. Fixed A-module-valued sheaves are the fixed-coefficient presentation
  of sheaves of modules over the constant sheaf A.
- The specified extension by zero is exactly the recorded `openImmersionLowerShriek`.
  Its definition is the localization presheaf left Kan extension followed by
  sheafification (`localizationLowerShriek_eq`); for a monomorphism the indexing
  category is empty or has a terminal object, giving the specified zero/M values.
- Exactness is the first two conjuncts, `PreservesFiniteLimits` and
  `PreservesFiniteColimits`, on this additive functor between abelian categories.
- The sheaf adjunction is `Nonempty (openImmersionLowerShriek ... j ⊣
  openImmersionRestriction ... j)`. The next conjunct is the adjunction on complexes.
  Restriction is evaluation along composition with j, the recorded inverse image
  for an open immersion.
- Degreewise action is the real definition `openExtensionCochain A j :=
  (openImmersionLowerShriek ... j).mapHomologicalComplex (.up ℤ)`.
  Thus its terms and differentials are j_! applied to those of K, in every integer
  degree; unbounded complexes are included.
- A geometric point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` with a map from
  `Spec (.of Ω)`. The in-U case is quantified over a lift `y : Spec (.of Ω) ⟶ U`;
  composition `y ≫ j` is its point on X. The functor isomorphism on complexes gives
  `(j_! K)_(y ≫ j) ≅ K_y`, naturally and with all differentials.
- The complementary case uses a point `y : Spec (.of Ω) ⟶ X` and
  `¬ ∃ z : Spec (.of Ω) ⟶ U, z ≫ j = y`, exactly lying outside the open subscheme.
  `IsZero` of the resulting stalk complex expresses vanishing in every degree.
- For every `(B : Type (u + 1)) [CommRing B] [Finite B] (φ : A →+* B)`,
  `openExtensionScalarMap φ j` is the mate of the identity on restricted sections,
  with direction `j_!^A Res_U ⟶ Res_X j_!^B`. The last conjunct states `IsIso`
  both on sheaves and after `mapHomologicalComplex`. Inverting this specified map
  gives exactly the node's canonical `Res_X j_!^B K ≅ j_!^A Res_U K`.

Dependency declarations read and used by the existing module:

- `def-weil-extension-by-zero`: the full definitions and docstrings in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`,
  notably `AlgebraicGeometry.ProEtale.openImmersionLowerShriek`,
  `openImmersionRestriction`, `localizationLowerShriek_eq`, and
  `openImmersionLowerShriekAdjunction`.
- `def-weil-pbc-proetale-site`:
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; the common underlying site is
  `Scheme.ProEt.topology`, supplied transitively through the stalk module.
  This statement is about complexes and uses the fixed-module presentation directly.
- `def-weil-pbc-scheme-conventions` is a convention record, with no declaration or
  import of its own. The relevant notions are `Scheme` and `IsOpenImmersion`.
- `def-weil-proetale-geometric-stalk`:
  `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`,
  `AlgebraicGeometry.Scheme.proEtaleGeometricNeighbourhoodForget`,
  `proEtaleGeometricStalk`, and `proEtaleGeometricFixedModuleStalk`.
  The helper `geometricModuleStalkFunctor` takes exactly their colimit diagram.
- `def-pc-sheaf-restrict-scalars` is a Mathlib leaf, recorded by its mathlib_match:
  `SheafOfModules.restrictScalars` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`. Its object keeps the
  underlying sheaf and composes its scalar action. In fixed coefficients the same
  operation is `sheafCompose ... (ModuleCat.restrictScalars φ)`;
  `ModuleCat.restrictScalars.smul_def` gives `a • m = φ(a) • m`.

Edge cases checked: the identity open immersion has only the inside case; the empty
open has only the outside case; the empty ambient scheme has no geometric points.
The zero ring and zero complex are allowed (no Nontrivial hypothesis). Arbitrary ring
homomorphisms, including the identity, are allowed; no injectivity or flatness is added.
All integer degrees are allowed. The site retains its object universe u+1 and morphism
universe u, with module values and neighbourhood colimits in u+1. No equality between
these universes or assertion of conservativity of ordinary geometric stalks is imposed.

Searches made via `msearch.py Q27 lem-cbc-proetale-extension-zero`:

- LeanFinder: "extension by zero on the small pro-etale site is exact left adjoint
  to restriction with geometric stalk formula and commutes with restriction of scalars".
  Eight hits, including Scheme.Modules restriction adjunctions and topological stalk
  adjunctions; none gives this pro-etale statement.
- Loogle: `SheafOfModules.restrictScalars, CategoryTheory.Adjunction`: zero hits.
- Mathlib grep: `extension[Bb]yZero|extension_by_zero|openImmersionLowerShriek|
  geometricModuleStalkFunctor`: zero hits.
- LeanSearch: "extension by zero pro-etale site exact left adjoint geometric stalk
  restriction scalars": unavailable, Internal Server Error; the other searches worked.
- Direct rg over upstream WeilConjectures and side lean/Sheaf:
  `lem-cbc-proetale-extension-zero|proEtale_extension_by_zero`. The older upstream
  checkout has no exact theorem. The side library has the exact theorem at the
  module and line above, and its later comparison module imports it.
- Read `coord/pefw-upstream-framework.md` and the relocated pro-etale Open.Defs module
  to verify the compatible published extension functor instead of a legacy duplicate.

No statement dispute or node fault was found. The reuse avoids any duplicate definition
or theorem. The required dry run checks the existing declaration and its recorded helpers
by importing the current published module and checking their full types.

## Second reading by Q27

I read the node, its source place, the dependency records, and the published declaration
`AlgebraicGeometry.ProEtale.proEtale_extension_by_zero` in
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`. The source assumptions are a finite
commutative coefficient ring, an open immersion of schemes, and the geometric-point
field hypotheses used in the two stalk cases. The item-by-item comparison is:

1. The coefficient object is `A : Type (u + 1)` with `[CommRing A] [Finite A]`.
   Lean has exactly these binders; verdict: holds, including the zero ring.
2. The geometric objects are `{U X : Scheme.{u}}`, `j : U ⟶ X`, and
   `[IsOpenImmersion j]`. Lean has exactly these objects and instance, with no
   separation, noetherian, quasi-compact, or finiteness assumption; verdict: holds.
3. The exactness clause says `PreservesFiniteLimits` and `PreservesFiniteColimits` for
   `openImmersionLowerShriek (ModuleCat A) j`. Lean has both conjuncts for the recorded
   extension-by-zero functor; verdict: holds.
4. The sheaf adjunction clause is
   `Nonempty (openImmersionLowerShriek (ModuleCat A) j ⊣
   openImmersionRestriction (ModuleCat A) j)`. Lean has this exact adjunction, with
   the recorded restriction functor; verdict: holds.
5. The degreewise-complex clause is
   `Nonempty (openExtensionCochain A j ⊣
   (openImmersionRestriction (ModuleCat A) j).mapHomologicalComplex (.up ℤ))`.
   The declaration defines `openExtensionCochain` as the recorded lower-shriek functor
   mapped to unbounded integer cochain complexes and states this exact clause; verdict:
   holds, including every integer degree.
6. For an inside geometric point, Lean quantifies
   `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and
   `y : Spec (.of Ω) ⟶ U`, then gives a `Nonempty` natural isomorphism between
   `openExtensionCochain A j ⋙ (geometricModuleStalkFunctor A (y ≫ j)).mapHomologicalComplex
   (.up ℤ)` and the stalk functor at `y`. This is the node's
   `(j_!K)_{\bar x} = K_{\bar x}` clause, with composition giving the point on X;
   verdict: holds.
7. For an outside point, Lean uses the same geometric-point binders with
   `y : Spec (.of Ω) ⟶ X`, assumes
   `¬ ∃ z : Spec (.of Ω) ⟶ U, z ≫ j = y`, and for every
   `K : CochainComplex (Sheaf (Scheme.ProEt.topology U) (ModuleCat A)) ℤ` states
   `IsZero` of its extended stalk complex. This is exactly the node's zero stalk clause;
   verdict: holds, with no point or complex case omitted.
8. For every `B : Type (u + 1)` with `[CommRing B] [Finite B]` and every
   `φ : A →+* B`, Lean states `IsIso (openExtensionScalarMap φ j)` and
   `IsIso` after `mapHomologicalComplex (.up ℤ)`. This is the canonical scalar
   restriction comparison in the node, in the stated direction; verdict: holds.

The source place is the blueprint node (order 1582), with the Stacks references Tags
09AE, 03DI, 03DJ, and 03CY. The dependency declarations were opened: the lower-shriek
definition supplies the specified sheafified extension presheaf and restriction,
the pro-etale site and geometric-stalk nodes supply the exact site and colimit stalk,
and Mathlib's `SheafOfModules.restrictScalars` supplies the scalar operation. Each is
the same notion as the node's dependency; no dependency repair or new node is needed.

Edge cases checked: identity and empty open immersions give respectively only the inside
and only the outside alternative; an empty ambient scheme has no geometric points; the
zero coefficient ring and zero complex are permitted; `n = 0` and all other integer
degrees are included; arbitrary coefficient maps, including the identity, are allowed;
and the site/module universes remain `u` and `u + 1` as required. No characteristic,
nontriviality, injectivity, flatness, or universe equality was added.

Searches were repeated with `msearch.py` (LeanFinder and LeanSearch), Loogle, and `rg`
over Mathlib, the upstream WeilConjectures sources, and `lean/Sheaf`. They found no
other declaration of this full pro-etale extension-by-zero statement. The published
module was also checked with `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`.

No mismatch was found. The sandbox node therefore records the already published
declaration with `existing: true`; no Lean module was copied or altered, and no
statement, dependency, or proof field was changed.
