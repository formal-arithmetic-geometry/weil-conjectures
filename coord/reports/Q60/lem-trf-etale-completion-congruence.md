## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCompletionCongruence` states
`AlgebraicGeometry.etale_completion_congruence`, with its single proof `sorry`.
It changes only the item's `lean` record. There are no new notions, auxiliary
definitions, dependency repairs or statement corrections.

This is the dispatched stage-2 task: the accepted O1 stage-1 split has no Lean
record and `coord/queue.tsv` lists this node at stage 2. The inherited stale
stage-1 assignment refusal does not prohibit this work (brief-stage2 §0).
No shared repository file was written and no direct git command was run.

Hypothesis and conclusion correspondence:

- Locally Noetherian base: `{S : Scheme.{v}} [IsLocallyNoetherian S]`.
- X and Y locally of finite type over S: explicit `sX : X ⟶ S`, `sY : Y ⟶ S`
  with `[LocallyOfFiniteType sX] [LocallyOfFiniteType sY]`.
- The etale chart: `p : U ⟶ X` and `[Etale p]`.
- The S-morphism f: `f : U ⟶ Y` with `hbase : p ≫ sX = f ≫ sY`.
  U's structure map is `p ≫ sX`; thus p and f are both S-morphisms.
- The point u is explicit. The points x and y are written as `p u` and `f u`.
  This eliminates only the named-point equalities p(u)=x and f(u)=y; any data
  with separately named x and y substitutes into this statement. Conversely
  these displayed images give such data. Applying hbase to u gives their
  common image in S, so the common-base-point clause is retained.
- The isomorphism on residue fields is `hres : IsIso (p.residueFieldMap u)`.
- A, B and C are precisely `Y.presheaf.stalk (f u)`,
  `X.presheaf.stalk (p u)` and `U.presheaf.stalk u`. Their maximal ideals are
  `IsLocalRing.maximalIdeal`; their completions are `AdicCompletion` with that
  ideal and that stalk, never arbitrary isomorphic rings.
- The canonical iota maps are `algebraMap` into these completions.
- The actual completed maps are the binders `phat` and `g` together with
  `hphat` and `hg`. For every n, every completed element z and every stalk
  representative of its nth quotient coordinate, their nth output coordinate
  is that representative's image under `(p.stalkMap u).hom` or
  `(f.stalkMap u).hom`. This is exactly the node's specification by all quotient
  maps. Quotient representatives exist, and equality of all coordinates is
  equality in AdicCompletion, so these conditions uniquely determine each map.
  They impose no extra mathematical assumption on the maps specified by the
  node. Existence is also supplied upstream by
  `RingHom.exists_adicCompletion_map_of_local`; no choice is used to construct
  unknown data in this module.
- The ring isomorphism phi is an arbitrary `≃+*` between Ahat and Bhat.
  No continuity or base-linearity assumption is added.
- The integer N >= 1 is `(N : ℕ) (hN : 1 ≤ N)`. This parametrizes exactly the
  positive integers, with no N=1 case omitted.
- The hypothesis for every a in A is `hcongr`; its ideal is
  `Ideal.map (algebraMap C D) (maximalIdeal C ^ N)`, namely m_C^N D.
- The first conclusion is `IsLocallyNoetherian Y` and the next three conjuncts
  are `IsNoetherianRing` of A, B and C, in that order.
- D is local: the existential witness `hlocal : IsLocalRing D` supplies its
  structure. The equality using `@IsLocalRing.maximalIdeal D _ hlocal`
  identifies its actual maximal ideal with `Ideal.map (algebraMap C D) m_C`.
  The explicit witness avoids presupposing the local structure being concluded.
- `Function.Bijective phat` says the completed chart map is a ring isomorphism;
  bijectivity of `phat.comp phi.toRingHom` says the same for alpha. These are
  the actual specified ring homomorphisms, so no unspecified isomorphism is
  substituted for either map.
- The final universal conclusion is `g z - phat (phi z)` in the Nth power of
  the actual maximal ideal supplied by hlocal, for every z in Ahat. Thus its
  ideal is n^N, rather than merely a coordinate-kernel ideal.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and
  `LocallyOfFiniteType.isLocallyNoetherian` (the latter is a proof dependency).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  exposed through Noetherian; no finite-type or quasi-compact strengthening.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, with its imported
  locally-finite-presentation and flat interfaces.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, whose defining map is the residue of the stalk map.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its algebraMap and `evalₐ`, exposed through `.LocalRing`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, exposed by these imports.
- The proof plan also imports the recorded modules for the affine-stalk
  identification (`Mathlib.AlgebraicGeometry.AffineScheme`), localization
  Noetherianness (`Mathlib.RingTheory.Localization.Submodule`), etale maximal
  ideals (`Mathlib.RingTheory.Unramified.LocalRing`), and
  `WeilConjectures.RingTheory.FlatLocalCompletionIso`, containing
  `RingHom.flat_local_completion_iso`.
- `AdicCompletion.maximalIdeal_eq_map` and local-completion structure are in
  `.LocalRing`; completion-mod-power's `pow_smul_top_eq_ker_eval` is exposed by
  its import of `.Completeness`. These proof imports preserve the accepted plan.

Source check: opened `literature/stacks-project/more-morphisms.tex` at
`lemma-isomorphism-approximation` (Tag 0CAV), including its full completion and
graded-ring argument. Its separate G-ring assumption constructs the initial
approximation; this item starts with the chart and congruence already given and
does not require that assumption. The accepted five-step split matches the
comparison by Tag 0AGX and the finite-quotient extension argument by Tag 05GG.
The latest blueprint is the snapshot named main-20261023-1620 in COMMITS.txt;
the current curve-zero unit does not spell out this historical local-model
sublemma, as already documented by its accepted split_report.

Edge cases checked before writing: N=1 is included (no N>=2 assumption is used
for extending congruence). Field stalks have zero maximal ideals and the
congruence becomes equality, consistently with their completions. Identity
charts and identity ring isomorphisms are included. Empty X, Y or U cannot
supply u and therefore produce no pointed instance, precisely as in the node.
There is no assumption of closed or rational points, an algebraically closed
field, global Noetherianness, finite type in place of local finite type,
separatedness, G-ring, or continuity of phi. All schemes use the usual common
Scheme universe, and all universes and variables are explicitly bound.

Searches made with the prescribed msearch.py wrapper (full results retained
in sandbox searches.jsonl):

- leanfinder: "An etale morphism with unchanged residue field gives isomorphic
  completed local rings and extends congruences to completions". Eight hits,
  including RingHom.Etale.respectsIso, Algebra.IsEtaleAt and standard-etale
  APIs; none states this comparison or the congruence extension.
- loogle: "AdicCompletion, IsLocalRing". Twelve hits, notably the local-ring
  instance, maximalIdeal_eq_map and residueField_map_bijective. These supply
  individual structures and clauses, not the entire node.
- grep: `(etale|Etale).*(complet|Complet)|(complet|Complet).*(etale|Etale)`.
  Five hits in Mathlib/RingTheory/Etale/QuasiFinite.lean, all concerning complete
  orthogonal idempotents rather than completed local rings.
- leansearch: "An etale local ring map with the same residue field induces
  isomorphic completions". Eight hits, etale and residue-field definitions and
  locality results, no exact theorem.
- rg of both lean/WeilConjectures and lean/Sheaf for etale/completion and
  completionMap, plus the exact node tag and proposed declaration name.
  No exact declaration. The existing `etale_completedLocalRing_iso` in
  Sheaf.AlgebraicGeometry.EtaleCompletedLocalRingIso was opened: it requires
  an algebraically closed base field and a rational-point condition, and has
  no congruence-extension conclusion, so cannot replace this general node.
  FlatLocalCompletionIso supplies only the algebraic comparison used in the
  proof, and CompletionMapForLocalHom supplies only coordinatewise-map
  existence. Neither is duplicated here.

Validation: prescribed scompile.py compiled both the sandbox and library module
successfully (4.8 and 6.2 seconds), with no errors or warnings. No diagnostic
commands are left in the delivered module. There is no STATEMENT-DISPUTED flag.

## Second reading by Q60

A separate second pass by this worker reopened the final Lean file and node and
checked each clause against the correspondence above; no second agent was
started, as expressly required by the dispatched brief. The maintainer's
independent delivery review remains the independent reading. This pass checked
in particular the direction of both stalk maps, the source and target of phi,
the occurrence of phi *inside* phat, the distinction between m_C^N D in the
hypothesis and the actual maximal ideal n^N in the conclusion, and that the
existential hlocal is used in both occurrences of the latter ideal. It also
checked that hphat and hg constrain every quotient coordinate, including n=0,
not merely the dense original-ring image; an arbitrary map agreeing only on A
would be insufficient. The named x,y equalities are eliminated by substitution,
not replaced by closed-point or rational-point restrictions. No mismatch or
statement correction was found.
