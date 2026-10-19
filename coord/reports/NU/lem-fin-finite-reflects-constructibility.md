## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleOfFiniteDirectImage` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_finite_lowerStar`.
Only its proof is `sorry`; no definitions or auxiliary theorems are introduced.

Hypothesis and conclusion correspondence:
- Schemes Z and S: `{Z S : Scheme.{u}}`, with explicit universe `u`.
- Both schemes Noetherian: `[IsNoetherian Z] [IsNoetherian S]`.
- The finite morphism p: `(p : Z ⟶ S) [IsFinite p]`.
- Finite commutative coefficient ring: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
- Etale module sheaf F on Z: `(F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  This is the sanctioned constructible-module encoding over the constant ring sheaf.
- Constructible direct image: `hF : IsConstructibleEtaleModuleSheaf
  ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).obj F)`.
- Conclusion: `IsConstructibleEtaleModuleSheaf F`.

The blueprint source was read at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-reflects-constructibility.md`.
It agrees with the node. The declaration docstring includes all four proof steps:
constructible pullback, the counit stalk projection, vanishing cokernel via exact
conservative stalks, and constructible kernel followed by constructible cokernel.

Statement dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, specialized to `ModuleCat Λ`.
  Its objectwise definition is sections on the base-change etale object.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, the exact finite
  stratification and finite constant module values definition.
- `def-weil-pbc-scheme-conventions` fixes no independent declaration.
- `def-weil-pbc-etale-sheaves` supplies the sanctioned Mathlib `CategoryTheory.Sheaf`
  encoding in its record; its upstream module is imported among proof dependencies.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.

Recorded proof-dependency modules are imported without `public`, including
ConstantSheaf, EtaleSheaves, ConstructibleSubsheafNoetherian, Finite.Stalk,
InverseImageStalkGerm, Sites.EtalePoint, ConstructibleSheaf.Pullback and
ConstructibleSheaf.KernelCokernel. Mathlib leaf proof dependencies are imported from
FinitePresentation, Point.Basic, Point.Skyscraper and ShortComplex.ShortExact.
The inverse-image functor is already in the public direct-image import.
No import cycle was found.

Edge cases: the empty source scheme is permitted (its sheaf is constructible with
an empty stratification); the empty target forces empty source. The zero sheaf and
the zero commutative coefficient ring are allowed. A finite map may have proper
closed image or empty fibres; no surjectivity instance is present. At a chosen
source point the fibre projection has the specified factor. Both Noetherian
hypotheses are kept exactly as stated even though finiteness makes the source
hypothesis follow from the target. No Nontrivial or characteristic hypothesis is
introduced. The coefficient and sheaf universes follow the dependency convention.

Searches for duplicates (2026-10-15):
- msearch leanfinder: "A finite morphism of noetherian schemes reflects
  constructibility of etale sheaves of finite ring modules under direct image".
  Eight results: scheme constructible-image/preimage and finite-type facts;
  none states constructibility reflection for module sheaves.
- msearch loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Etale.lowerStar`.
  Zero hits; lowerStar is unknown to the Mathlib-only index.
- msearch grep: `constructible.*(pushforward|direct.image)|reflect.*constructib`.
  Zero hits.
- rg of upstream WeilConjectures and project lean/Sheaf for reflection,
  constructibility with lowerStar and this node id: unrelated direct-image
  preservation, closed-immersion preservation and coefficient-control facts;
  no matching theorem. Read ConstructibleSheaf/OpenClosed.lean and
  ConstructibleSheaf/FinitePushforward.lean candidates: preservation and
  embeddings, not the requested reflection theorem.
- rg for the new declaration name in Mathlib/upstream name index and project
  modules: no conflicting declaration.

No statement correction, new node, dependency module or statement dispute is needed.
Server single-file compile succeeded cleanly (nice 19, two threads, 60 seconds).

## Second reading by NU

Read the node, its original blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-reflects-constructibility.md`,
the five statement-dependency nodes and their recorded declarations. The source
is a standalone lemma, with no additional section-wide assumptions. Also read
Stacks `etale-cohomology.tex`: 03QP (finite stalk formula), 03RU (module local
constancy), 095E (global constructible partition), 095G (pullback), 03RZ
(kernel/cokernel), and 09BH (Noetherian subobjects). Their coefficient-ring
Noetherian hypothesis follows from finiteness; no extra hypothesis is needed.

Object, hypothesis and conclusion checklist (all pass):

- Arbitrary schemes Z and S: `{Z S : Scheme.{u}}`. Neither is restricted to
  varieties, curves, schemes over a field, nonempty schemes or separated schemes.
- Both are Noetherian: `[IsNoetherian Z] [IsNoetherian S]`. Read Mathlib's class
  in `AlgebraicGeometry/Noetherian.lean`: locally Noetherian and quasi-compact,
  exactly Noetherian schemes. Both binders are in the node, even though finiteness
  would make the source hypothesis follow from the target hypothesis.
- Morphism p from Z to S: `(p : Z ⟶ S)`, with `[IsFinite p]`. Read Mathlib's
  `IsFinite` signature and fields: affine morphism and finite maps on sections
  over affine opens, precisely `def-weil-finite-integral-morphism`. No
  surjectivity, etaleness or flatness assumption has been introduced.
- Finite commutative coefficient ring Lambda:
  `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`. This allows the zero ring and
  every characteristic, with no field or Nontrivial assumption.
- Etale sheaf of Lambda-modules F on Z:
  `(F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  The module-valued encoding is expressly authorized in the recorded
  `def-weil-pbc-etale-sheaves` convention for constructible/six-functor material;
  this is not an O_Z-module or a pro-etale sheaf.
- The sole conditional hypothesis, constructibility of p_*F, is exactly
  `(hF : IsConstructibleEtaleModuleSheaf
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).obj F))`.
  Read `Etale.lowerStar` in `UpperLowerStar/Defs.lean`: its object is precomposition
  with base change, so on an etale V over S its sections are F(V times_S Z).
  Its coefficient-category structures are supplied for ModuleCat; the statement
  adds no independent existence or exactness instance.
- The entire conclusion is `IsConstructibleEtaleModuleSheaf F`, without an
  additional clause or weakened predicate. Read the dependency's full definition:
  a finite locally closed scheme partition, constructibility of each underlying
  subset, and etale trivializations by finite constant Lambda-modules on every
  stratum. Read `LocallyClosedStratification` and `LocallyConstantDatum` as well:
  they supply genuine immersion and cover data, with no hidden closure-incidence
  condition. This renders the node's exact constructibility notion on both sides.
- Quantifier order is schemes, p, coefficients, F, constructibility of p_*F,
  then constructibility of F. The commutation of independent coefficients and p
  in the source wording has no mathematical effect.

Edge cases pass. An empty source, an empty target (forcing the source empty),
the zero sheaf, the zero ring, non-surjective finite maps and empty fibres are
all permitted. `LocallyClosedStratification.n : Nat` allows n = 0, and the
stratum clauses quantify over `Fin n`; there is no nonemptiness condition.
For the proof's stalk projection a chosen source point supplies its own factor.
No characteristic assumption occurs. The explicit universe u is arbitrary and
all objects and coefficients follow the exact dependency universes. A finite
ring can be represented at that coefficient universe, and arbitrary scheme
universes can be placed in a common universe. There are no independent test-object
universe restrictions, free variables, or unbound universes in the signature.

Independent duplicate searches (2026-10-15):

- msearch leanfinder: "Constructibility of a sheaf of modules is reflected by
  pushforward along a finite morphism of schemes". Eight hits, including
  constructible images of subsets and general module pushforwards; no reflection
  theorem for etale module sheaves.
- msearch loogle: `IsConstructibleSheaf`. No hits; the Mathlib index does not
  know this project predicate.
- msearch grep: `constructible.*finite|finite.*constructible`. Thirteen Mathlib
  hits, all constructible subsets or finite-union/intersection facts.
- rg of the entire upstream WeilConjectures tree, project lean/Sheaf, Mathlib,
  and upstream name index for reflection and constructibility with lowerStar.
  Opened `Curve/FinitePushforwardModuleConstructibleReflection.lean`:
  `Scheme.isConstructibleSheaf_of_finite_lowerStar_module` requires a map to
  Spec k with IsCurve and k algebraically closed. It therefore does not state
  this arbitrary-Noetherian-scheme node, even though its coefficients are more
  general. It also uses the upstream constructibility predicate rather than the
  exact dependency predicate. Opened upstream ConstructibleSheaf/Defs.lean to
  check that distinction. Other candidates give preservation or embeddings;
  there is no usable existing declaration and no name collision.

No new definition node or dependency module is delivered, and no dependency
repair or statement correction is needed. The only delivered theorem has its
whole proof `sorry`; there are no definitions, private substitutes, local
notation, instances, or auxiliary proofs. The source/blueprint docstrings and
all four node proof steps are present, including the germ-compatible counit
projection, exact-stalk cokernel argument and constructible kernel/cokernel.
Imports include the recorded statement and proof dependencies, with the latter
non-public. No mathematical or syntactic mismatch was found; the Lean and node
were left unchanged. The report is supplemented by this reading and by the
curve-specific duplicate exclusion omitted from the worker's search discussion.

Verification: `lean.statement` is verbatim the theorem signature; every Lean
line has at most 100 characters. The sole delivered file was compiled using
scompile.py on the server: 1.5 seconds, nice 19, two threads, 60-second per-file
limit, no errors or warnings. The original Worker report remains above.
