## Worker report

The module `Sheaf.AlgebraicGeometry.VersalFormalObjectQuasiInitial` states
`AlgebraicGeometry.ArtinDeformation.exists_formalObjectMap_of_isVersal`, with
`sorry` as its sole theorem proof. It also supplies `FormalObjectMap`, the morphism
notion explicitly described in this item's statement. No statement correction,
new DAG node, dependency replacement, or disputed statement is needed.

Source read: `literature/stacks-project/formal-defos.tex`,
`lemma-versal-object-quasi-initial` (Tag 06HT), together with
`lemma-smooth-morphism-essentially-surjective` (06HN) and `remark-versal-object`
(06HS). These give exactly the successive specified-lifting argument in the node.
The theorem docstring records all five proof steps and their dependencies.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Commutative Noetherian base ring R | `{R : Type u}`, `[CommRing R]`, `[IsNoetherianRing R]` |
| Field l finite as an R-module | The binder named `k`, `[Field k]`, `[Algebra R k]`, `[Module.Finite R k]` |
| Test category and covariant groupoid transport | Imported `TestCategory` and `CofibredGroupoids.{u, v, w} R k` |
| F is a predeformation category | `(F : CofibredGroupoids ...) (hpre : IsPredeformation F)` |
| C and D complete Noetherian local marked R-algebras | `(C D : CompleteLocalAlgebra R k)`; its fields are `ring`, `localRing`, `noetherian`, `complete`, `residueEquiv` |
| Formal object xi over C, and arbitrary eta over D | `(ξ : FormalObject F C)` and `(η : FormalObject F D)` |
| xi is versal | `(hξ : IsVersal ξ)`, the imported specified-isomorphism lifting property |
| A morphism includes a local R-map C to D | `FormalObjectMap.hom : C.ring →ₐ[R] D.ring` and `localHom : IsLocalHom hom` |
| Its map preserves the specified residue field | `marked`, equality after the two `residueEquiv` identifications |
| Evaluation along C to D/m_D^n for every positive n | `atLevel` and `atLevel_hom`; the latter fixes each map to `(Ideal.Quotient.mkₐ R ...).comp hom` |
| Isomorphisms from those evaluations to eta's levels | `app : ∀ n : ℕ, evaluate ξ (atLevel n) ≅ η.obj n` |
| Compatibility at all levels | `comm` for every `h : n ≤ m`, using imported `evaluationRestriction` and `η.transition h` |
| A morphism xi to eta exists | `Nonempty (FormalObjectMap ξ η)` |
| In particular the underlying ring map is local and residue preserving | The `hom`, `localHom`, and `marked` projections of the resulting morphism |

The auxiliary structure belongs to this node's explicitly stated morphism notion.
The imported `FormalHom` handles only two objects over the SAME complete ring and
cannot encode C to D; it is not replaced or duplicated here. The `atLevel` fields
are convenient dependent-type witnesses for the unique quotient composites,
not arbitrary maps: `atLevel_hom` fixes their data exactly. `atLevel_comm` is the
forced quotient-map equality used as an argument of `evaluationRestriction`.
Locality and marking of these composites follow from locality and marking of
`hom`; the quotient identities follow on representatives. Consequently these
fields add no mathematical hypothesis to the definition of a morphism.
Every isomorphism is actual data, with every compatibility equation retained;
there is no replacement by unrelated per-level existence statements.

Recorded dependency declarations read and used:

- `def-sfb-artin-deformation-test-category`:
  `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`, namespace
  `AlgebraicGeometry.ArtinDeformation`; `CofibredGroupoids`, `IsPredeformation`,
  `CompleteLocalAlgebra`, `FormalObject`, `LocalMap`, `levelTest`, `levelMap`,
  `map`, `push`, `evaluate`, `evaluationRestriction`, and `IsVersal`.
  Read their full signatures and docstrings, including positive-level indexing,
  the residue marking, pseudofunctor comparison direction, and restriction formula.
- `def-weil-pbc-noetherian-ring`: Mathlib
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`, through the public
  dependency import. This is the all-ideals-finitely-generated notion.
- `def-weil-field`: Mathlib `Field` from `Mathlib.Algebra.Field.Defs`, through
  the public dependency import. It includes commutativity and nontriviality.
- `def-weil-pbc-adic-completion`: Mathlib
  `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete` and
  `AdicCompletion`. `CompleteLocalAlgebra.complete` uses maximal-ideal completion;
  read both the compatible-sequence definition and the completeness classes.
- `def-weil-finitely-generated-module`: public import
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.
  `Algebra.FiniteType R k`, needed by the test-category interface, is inferred
  from this finite-module hypothesis; it is not a further assumption.
- Proof dependency `lem-weil-pbc-noetherian-local-quotient-artinian-local`
  is a Mathlib leaf recorded on
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing` in
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`; this module is a plain proof
  import. Its general ideal-containment formulation was read in the DAG.

Edge cases checked before drafting: D equal to the marked residue field (all
levels constant); D = k[e]/(e^2) (eventually constant levels and nontrivial early
transitions); D = k[[t]] (a genuinely infinite compatible tower); C = D and the
identity underlying map; equal levels m = n; positive exponents start at one,
encoded by n = 0. No assumption on characteristic is imposed. The zero ring
cannot carry the specified field residue and is already excluded by the node.
The ring/test universe is the shared u of the recorded dependency; fibre object
and arrow universes v and w remain independent and explicit. There is no empty
index-set assumption or nonzero tangent-space restriction. The theorem promises
existence and makes no uniqueness claim.

Searches actually run using the prescribed msearch wrapper:

- LeanFinder: `A versal formal object maps to every formal object over a complete
  Noetherian local algebra`: eight results, including `Algebra.FormallySmooth`
  and its adic lifting theorems; none concern a general predeformation groupoid.
- Loogle: `IsVersal, FormalObject, IsLocalHom`: zero hits; reported unknown
  identifier `IsVersal` (the project declaration is outside the Mathlib index).
- Mathlib grep: `versal|FormalObject|quasi.?initial`: 25 hits, all unrelated
  occurrences of universal properties or reversal; no exact match.
- LeanSearch: `A versal formal deformation admits a compatible morphism to every
  formal deformation over a complete local algebra`: eight results about formally
  smooth algebras and scheme limits; no deformation-groupoid result.
- Direct `rg` on `lean/WeilConjectures` and `lean/Sheaf` with
  `FormalObject|\b[Vv]ersal\b|quasi.?initial|versalFormal|FormalObjectMap|FormalMorphism`
  found the recorded Artin-deformation framework and distinct scheme-based
  Artin/stack versality interfaces, but no inter-base morphism or this theorem.
- Direct `rg` for both proposed full declaration suffixes in Mathlib,
  `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json`: no matches.
- `grep -rn` for the item id in `lean/WeilConjectures`: no match.

Only the item's `lean` record is changed. Both helper and theorem are listed in
`lean.declarations`; the recorded theorem signature is copied verbatim from the
file. No upstream source or shared repository file was modified directly.

Validation: the prescribed `scompile.py` check compiled this module cleanly in
both sandbox and library modes. The `deliver2.py --no-push` dry run passed the
server preflight and compile, printing OK. A local read-only check found no Lean
line longer than 100 characters, confirmed the recorded signature verbatim, and
confirmed that `lean` is the only changed field of the existing node. The delivery
wrapper supplies the direct-worker review notice; independent review belongs to
the maintainer, as specified in the dispatcher brief.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
