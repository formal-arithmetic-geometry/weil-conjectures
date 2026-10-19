## Worker report

The delivery states `AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_finite_torsion_cd`
in `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`. Its proof is `sorry`, with all
eight DAG proof steps copied into the declaration docstring. The canonical map is constructed
in the new definition module described below, rather than supplied as a hypothesis.

Hypothesis and conclusion correspondence:
- “X a scheme”: `X : Scheme.{u}`.
- “quasi-compact”: `[CompactSpace X]`, the recorded scheme convention.
- “quasi-separated”: `[QuasiSeparatedSpace X]`, the recorded scheme convention.
- “kuncd(X) < infinity”: `hcd : X.torsionEtaleCohomologicalDimension < ⊤`, using
  the dependency's actual numerical `ℕ∞` definition, not a substitute bound predicate.
- “Λ a torsion ring”: `Λ : Type (u + 1)`, `[CommRing Λ]`, and
  `hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0`. The coefficient-ring commutativity is the
  convention of def-kun-derived-tensor. This is equivalent to additive torsion for a
  unital ring: apply additive torsion to 1 to get n, and multiply n·1=0 by any element.
  Conversely n kills every element. No finiteness or invertibility of n is imposed.
- “E in D(X_et,Λ)”: `E : DerivedCategoryModule Λ X`, exactly the recorded
  ModuleCat-valued-sheaf encoding, with no boundedness condition.
- “K in D(Λ)”: `K : DerivedCategory (ModuleCat.{u + 1} Λ)`, unbounded.
- “RΓ(X_et,E) tensor^L K”: the source of `constantDerivedProjectionMap` uses
  `curriedTensor` on the upstream K-flat monoidal structure of the module derived category,
  applied to `(rightDerivedGlobalSections (ModuleCat Λ) X).obj E` and K.
- “RΓ(X_et,E tensor^L K_underlined)”: its target uses `curriedTensor` of the same upstream derived
  monoidal structure as the dependency's `Etale.derivedTensor`, with the existing left derived constant-sheaf functor applied to K.
  The exact-functor identification `leftDerivedFunctorIsoMapDerivedCategory` identifies
  this functor with `mapDerivedCategory`, which applies the constant-sheaf functor termwise.
  `mapDerivedCategoryFactors` identifies it on representing cochain complexes with the
  dependency's `Functor.mapHomologicalComplex` constant-complex construction. Thus the
  displayed target is canonically the node's object; no different coefficients or complex
  construction is introduced.
- “the canonical map is an isomorphism”: `IsIso (constantDerivedProjectionMap Λ X E K)`.
  The map is `Adjunction.rightAdjointProjectionMap` of the existing derived adjunction,
  whose component is its Hom-equivalence applied to the canonical
  derived comonoidal comparison followed by tensoring its counit with the identity.
  This is exactly Stacks 0B56 specialized to the terminal geometric morphism, as in 0F12.

Dependency declarations read and used:
- def-weil-pbc-scheme-conventions: its convention record; `Scheme`, `CompactSpace` and
  `QuasiSeparatedSpace`. It intentionally has no module or declaration of its own.
- def-kun-cd: `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`,
  `AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension` and its bound predicate
  from `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`.
- def-weil-pbc-derived-categories: `Sheaf.AlgebraicGeometry.DerivedCategories` and the
  imported upstream `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- def-weil-abstract-derived-category: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`.
- def-kun-derived-tensor: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`; it is `curriedTensor` of the existing
  unbounded K-flat derived monoidal category. The coefficient-side tensor is the same
  upstream construction specialized to ModuleCat.
- def-kun-constant-sheaf: `Mathlib.Algebra.Homology.Additive`,
  `CategoryTheory.Functor.mapHomologicalComplex`, specialized to the actual
  `constantSheaf X.smallEtaleTopology (ModuleCat Λ)`; its exactness instances are in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.
- def-weil-pbc-global-sections-functor: `Mathlib.CategoryTheory.Sites.GlobalSections`,
  `CategoryTheory.Sheaf.Γ` and `constantSheafΓAdj`; unbounded RΓ is the existing
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` from Derived.LowerShriek.
- The new definition node supplies `constantDerivedProjectionMap` without changing any
  recorded dependency or duplicating a derived category, tensor product, or constant sheaf.

All recorded proof-dependency modules are imported without `public` unless already a
public statement import. The generic ringed-projection-mate theorem has no recorded module;
there is no import to add for it. It remains a proof dependency for the exactness argument.
It is not needed to define this specialized map: the existing generic tensor comparison,
exact-left-adjoint derived adjunction and Hom-equivalence directly give its construction.
No wait on that unstated theorem is left.

Edge cases checked before writing: empty X remains allowed; its sheaf category is zero.
E=0 and K=0 remain allowed. The zero coefficient ring satisfies the torsion hypothesis
with n=1. Infinite torsion rings, such as polynomial rings over a finite field, are allowed.
No condition on torsion order relative to residue characteristics is imposed. Finite cd=0
is included. Both derived objects may be unbounded in both directions. There is no nonempty
scheme hypothesis. The chosen site and coefficient universes are precisely those of the
recorded dependency interfaces, with site morphisms in u and coefficients in u+1; a larger
universe can accommodate arbitrary source data. `autoImplicit` is disabled by the prescribed
compiler wrapper and every universe and variable in the files is explicitly bound.

Searches for the item (msearch.py):
- LeanFinder, “Derived global sections on a scheme of finite torsion etale cohomological
  dimension commute with derived tensor by an arbitrary constant complex over a torsion
  ring”: eight hits, on Kähler differentials and generic Tor, no matching statement.
- Loogle, `"projectionFormula"`: zero hits.
- Mathlib grep, `projectionFormula|pull.out.constant|globalSections.*tensor`: zero hits.
- LeanSearch, “Derived global sections tensor constant complex projection formula”:
  unavailable, Internal Server Error. This is recorded as unavailable, not a negative search.
- rg of upstream WeilConjectures and side lean/Sheaf for projection maps and RΓ/tensor:
  scheme-morphism projection formulas exist, but no theorem with these hypotheses and no
  terminal-site constant-coefficient projection map. Searching the exact item id in upstream
  likewise found no declaration. All search wrapper outputs are retained in searches.jsonl.

No statement dispute or correction: the statement agrees with the local Stacks Tag 0F12
and the blueprint unit. No original statement, proof, proof_deps or dependency node changed.

## New nodes

`def-kun-constant-projection-morphism` defines the canonical terminal-site morphism needed
by the item. Its module is `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`. The source
is Stacks 0F12 and the constructions of 07A4, 07A6 and 0B56, whose local passages were read.
Its statement also specifies the normalized ordinary constant-presheaf monoidal core and
flat preservation, the two proof obligations needed by the generic derivation API. The
module contains exactly two `sorry` theorems, each with a complete natural-language proof
and this matching DAG node: `exists_etaleConstantPresheafCoreMonoidal` and
`etaleConstantSheaf_preservesFlat`. They postpone only proofs of the stated construction
properties. The core existence theorem fixes every unit and tensor hom component to the
identity, so its data are determined uniquely: natural transformations are determined by
components; inverse maps of an isomorphism are unique; all remaining fields are proofs.
`Classical.choose` therefore chooses that specified core, not an arbitrary monoidal map.
The monoidal constant-sheaf structure is its composite with existing monoidal sheafification.
The derived comparison itself is `Functor.leftDerivedTensorComparison`, with its existing
characterization by the ordinary comparison on K-flat models; the derived adjunction is
the existing `Adjunction.derivedAdjunction` applied to `constantSheafΓAdj`. Every definition has real data and no proof hole in its body.

Searches for this node: LeanFinder returned eight hits on LightCondensed monoidal
structures, module pullback units and a Cartesian sheaf constraint; no terminal etale
comparison. Loogle `"constantSheaf", "Monoidal"` and Mathlib grep
`constantSheaf.*(Monoidal|PreservesFlat)|constant.*DerivedProjection` returned zero hits.
LeanSearch for the same notion was unavailable (Internal Server Error). Direct rg searches
of the upstream and side libraries found the generic derived comparison and adjunction
APIs used here, and a private constant-sheaf monoidal instance in
`Sheaf.ConstructibleSheaf.ConstantFiniteFreeDualNaturality`; that private instance cannot
be imported as an interface. No public normalized constant-presheaf structure, flat
preservation instance or terminal-site projection map exists. DAG searches and
`tools/blueprint_refs.py search 'constant projection'` found no node for this specialized
construction. The existing `def-kun-projection-formula-map` is specifically for a morphism
of schemes, with both arguments sheaf-derived objects; it does not give the terminal
geometric morphism to Sets with K in D(Λ). The generic ringed exactness theorem is a proof
node, not a second definition of this specialized constant-coefficient map. The new node
cites each existing notion it uses and is added to the item's stmt_deps.

The adjunction and mate helpers are parameterized by a coefficient category A, with the
standard monoidal Grothendieck hypotheses and a monoidal flat-preserving constant functor.
This is the generality of the existing upstream APIs and avoids repeated kernel expansion
of the concrete coefficient instances. In the item's signature A is specialized to
ModuleCat Λ; all instances are inferred from the existing module-category infrastructure
and the two construction properties supplied in this delivery. None is an added hypothesis
of the item. No compilation limit was raised, and all profiling settings remain only in
scratchpad files, outside the delivered Lean modules.

## Second reading by NA

I read the sandbox node and both modules independently, then the blueprint node and
Stacks etale-cohomology.tex, lemma-pull-out-constant-mod-n (Tag 0F12), including its
entire proof. I also read conventions.tex (rings are commutative, unital, and include
the zero ring), sites-cohomology.tex, lemma-pullback-tensor-product (07A4),
lemma-adjoint (07A6), and equation-projection-formula-map (0B56). The source has no
standing Noetherian, finite-type, properness, or invertibility hypothesis here.

Statement inventory and correspondence, in the node's order:

1. Scheme X: `(X : Scheme.{u})`. Verdict: same scheme and small etale site.
2. X is quasi-compact: `[CompactSpace X]`. Verdict: exact scheme convention.
3. X is quasi-separated: `[QuasiSeparatedSpace X]`. Verdict: exact scheme convention.
4. Finite torsion etale cohomological dimension: the named hypothesis
   `hcd : X.torsionEtaleCohomologicalDimension < ⊤`. Verdict: exact. I opened
   `TorsionEtaleCohomologicalDimension.lean` and `CohomologicalDimension.lean`:
   the former takes the infimum in `ℕ∞` of nonnegative integer bounds, using the
   latter's vanishing condition on every torsion abelian etale sheaf. Thus this is
   the numerical dimension of def-kun-cd, including dimension zero.
5. Torsion ring Λ: `(Λ : Type (u + 1)) [CommRing Λ]` and
   `hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0`. Verdict: exact. Commutativity and a unit
   are the Stacks convention and def-kun-derived-tensor's convention, not additional
   restrictions. An additively torsion unital ring has its unit killed by one positive
   integer; conversely such an integer kills every element by multiplication.
6. Arbitrary E in D(X_et,Λ): `(E : DerivedCategoryModule Λ X)`. Verdict: exact,
   without cohomology or boundedness conditions. I opened the actual upstream
   Coefficients.lean abbreviation: it is the derived category of
   `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. I also opened the recorded
   `Sheaf.AlgebraicGeometry.DerivedCategories` module; no alternate module-sheaf
   encoding is substituted.
7. Arbitrary K in D(Λ): `(K : DerivedCategory (ModuleCat.{u + 1} Λ))`.
   Verdict: exact unbounded cochain-derived category. Mathlib's DerivedCategory.Basic
   localizes integer cochain complexes at quasi-isomorphisms. E and K are independently
   universally quantified, after the hypotheses, just as in the node.
8. Left object RΓ(E) tensor^L K: expand the source of `constantDerivedProjectionMap`.
   It is `curriedTensor (DerivedCategory (ModuleCat Λ))` applied to
   `(rightDerivedGlobalSections (ModuleCat Λ) X).obj E` and K. Verdict: exact.
   I opened LowerShriek.lean: this RΓ is the total right derived functor of
   `Sheaf.Γ`. GlobalSections.lean defines Γ as right adjoint to constant sheaves and
   identifies it canonically with sections at the terminal site object.
9. Right object RΓ(E tensor^L K-underlined): expand the map's target. Its inner
   tensor is the same `curriedTensor` used by the recorded upstream `derivedTensor`
   in Etale.Derived.Tensor. Its second factor is the left derived constant-sheaf
   functor on K. Verdict: exact under the canonical identification with termwise
   constant complexes. I opened ConstantSheafOver.lean's finite-limit and finite-colimit
   preservation instances, LeftDerivedFunctor.MapDerivedCategory.lean's
   `leftDerivedFunctorIsoMapDerivedCategory` and its factorization, and the recorded
   constant-complex construction. Exactness makes this precisely the constant complex
   in def-kun-constant-sheaf, including unbounded K.
10. The specified canonical arrow is an isomorphism:
    `IsIso (constantDerivedProjectionMap (ModuleCat.{u + 1} Λ) X E K)`.
    Verdict: exactly this map, not existence of some isomorphism. I opened
    Adjunction.ProjectionMap.lean: `rightAdjointProjectionMap` takes the Hom-adjoint
    of the tensor comparison followed by tensoring the counit with the identity.
    I opened DerivedCategory.Adjunction.lean's `derivedAdjunction` and
    LeftDerivedFunctor.Monoidal.lean's `leftDerivedTensorComparison`, including
    `leftDerivedTensorComparison_app_app_comp_counit`. The latter derives the
    ordinary comonoidal constraint with its prescribed localization comparisons.
    This is the composite in 0B56 and hence the canonical arrow of 0F12.

The dependency node records and their actual source signatures were read, rather than
inferred from their names: scheme-conventions is a convention-only record; def-kun-cd,
derived-categories, abstract-derived-category, derived-tensor, constant-sheaf, and
global-sections are the exact declarations described above. The last is a Mathlib leaf
through its `mathlib_match`, rather than a missing declaration. The item's existing
statement and proof dependencies remain unchanged except for the worker's addition
of the new definition node. The recorded proof-dependency modules are imported; the
still-unstated generic ringed-projection-mate-exact has no module to import and is
not used to define the canonical map.

New-node reading (H12/H13): I read def-kun-constant-projection-morphism as a new stage-1
node against 07A4, 07A6, 0B56, and 0F12. Its six cited definition dependencies exactly
match its stmt_deps. Its id, chapter/unit, creation record, blueprint ancestry
(`blueprint_refs.py ancestor lem-kun-0f12`), empty proof fields, null mathlib_match,
none audits, and Lean record have the required shape. There is no dependency module
in this delivery. The coefficient-generic adjunction/map helpers specialize to
ModuleCat Λ; none of their Grothendieck, monoidal, resolution, or constant-functor
instances becomes an additional hypothesis of the item. The compiled `#check @...`
signature confirms this explicitly.

I checked the new module's data rather than accepting the report's assertion of
canonicity. In Mathlib's `Functor.CoreMonoidal`, the only data are εIso and μIso;
all other fields are proofs. The existence theorem fixes every hom component to
identity. Natural transformations are determined by components, and inverses to
fixed isomorphism homs are unique. Thus Classical.choose selects a fully determined
core, as allowed by AGENTS.md §5; it does not select arbitrary data from bare existence.
Sheafification uses the existing monoidal construction. Flat preservation is a named
sorry theorem with the stalkwise proof in its docstring, and is explicitly part of the
new node's statement. The second named sorry theorem is the normalized core existence
property, also explicitly part of that statement and with its complete proof docstring.
The remaining definitions contain real data and no sorry. No theorem has been proved.

Edge cases: X may be empty; no nonemptiness assumption is introduced. E or K may be
zero and may be unbounded in either direction. The zero coefficient ring is allowed
(n=1), as are infinite torsion rings (for example polynomial rings over finite fields).
No torsion-order invertibility or restriction on residue characteristics occurs.
The finite dimension can equal zero. There is no index parameter in the statement;
the proof and its docstring include empty sums. The site is the existing small etale
site (objects in u+1, morphisms in u), with module coefficients in u+1 as required by
the recorded derived-category interface. These are the existing size conventions,
not an added equality of object and morphism universes. Both Lean files explicitly
bind their universe variables; the elaborated item has only the hypotheses listed
above and no hidden instance or auto-implicit argument.

Independent searches, with different wording from the first worker:

- LeanFinder via msearch.py: “Unbounded etale cohomology projection morphism is
  invertible when the scheme has bounded torsion cohomology and the coefficient ring
  has positive characteristic”. Eight etale-locus/formal-etaleness hits; none states
  this derived projection formula.
- Loogle via msearch.py: `"constantSheaf", "tensor"`: zero hits.
- msearch grep: `rightDerivedGlobalSections|rightAdjointProjectionMap`: zero hits
  in its search scope. I supplemented this with direct rg of upstream and side Lean,
  which does find the generic APIs used by this delivery.
- LeanFinder for the new core: “Strong monoidal structure on a constant functor into
  a presheaf category with pointwise tensor product”. Eight hits: pointwise tensor,
  presheaf-of-modules monoidal structures, Cartesian sheaf inclusion, and condensed
  functors. None supplies a public normalized constant-module functor core.
- Loogle: `"Functor.const", "Monoidal"`: zero hits.
- LeanSearch: “global sections derived tensor with a constant complex finite
  cohomological dimension”: service unavailable (Internal Server Error), recorded
  as unavailable, not a negative mathematical result.
- Direct rg of Mathlib, upstream WeilConjectures and side lean/Sheaf using
  `projection.?formula`, `rightAdjointProjectionMap`, `pull.out.constant`,
  constant/Monoidal, and constant/PreservesFlat: the upstream scheme-morphism
  projection formula has extra scheme-morphism/compactification or finite-coefficient
  hypotheses and is not this terminal-site statement. I opened its relevant
  signatures. The private local constant-sheaf monoidal instance in
  ConstantFiniteFreeDualNaturality.lean has no reusable public interface; I opened
  its body and checked that its identity tensor constraints agree with this core.
  There is no public duplicate core, flat-preservation theorem, or specialized map.
- Direct DAG search and `tools/blueprint_refs.py search 'constant projection'`
  found no existing node for this specialized terminal-site map. The existing
  def-kun-projection-formula-map takes a morphism of schemes with two sheaf-derived
  inputs, not K in the coefficient derived category, and is not a replacement.

Mismatch and repair: no mathematical or signature mismatch was found. One H8
presentation omission was repaired: the eight-step theorem docstring carried the
proof text but did not explicitly name the DAG nodes used by each step. I added
those dependency ids to all eight steps. No statement, construction, hypothesis,
node statement, or dependency changed in this second reading; no statement_change
or citer audit is needed. Both lean.statement records were compared verbatim with
the corresponding source signatures and match.

Validation: scompile.py compiled both delivered siblings separately in dependency
order, cleanly, within the default 60 seconds. A scratch-only `#check @...` probe
also compiled and displayed the elaborated item, map and flat-preservation signatures;
it confirmed the item has precisely its displayed arguments. Both delivered modules
were recompiled after the docstring edit, with no warnings or errors. All module and
declaration docstrings carry source places and their own blueprint ids; all delivered
Lean lines are at most 100 characters. The scratch probe is not part of the delivery.
