## Worker report

The module `Sheaf.AlgebraicGeometry.StackAffineSourceNerveGeometry` supplies
`CategoryTheory.stack_affine_source_nerve_geometry`, with proof `sorry`, and the real
recursive construction `CategoryTheory.stackAffineSourceNerve`. The node is unchanged
except for `lean`. No new nodes or dependency repairs are needed. The helper is precisely
the term-and-augmentation construction in this node, not a second definition of stacks,
spaces, representability, quasi-compactness, or quasi-separatedness.

Hypothesis and clause correspondence:

- Size convention: explicit `universe u v w t s`; `Scheme.{u}` and independent
  `BasedCategory.{v,w}`. The input and output quasi-compactness predicates explicitly
  include `t,s`, preserving arbitrary enlarged test bounds. No equality of stack and
  site universes is assumed.
- Base scheme S: `{S : Scheme.{u}}`. Affine S-schemes T,V are `T V : Over S` with
  `[IsAffine T.left] [IsAffine V.left]`. No separation on S is imposed.
- Algebraic stack A: `A : BasedCategory.{v,w} (Over S)` and
  `hA : IsAlgebraicModuliStack A`. Its map to T is the actual based functor `h`.
- Quasi-compactness and quasi-separatedness of h are `hhqc` and `hhqs`, using
  `IsQuasiCompactAlgebraicModuliMap` and `IsQuasiSeparatedAlgebraicModuliMap`.
- Arbitrary v: the binder `a : BasedFunctor (discreteModuli (yoneda.obj V)) A` has
  no smoothness, representability, surjectivity, or finite-type assumption.
- Every p >= 0: `p : ℕ`. `stackAffineSourceNerve a p` consists of a total category
  and its based augmentation to A. The zero term is the canonical presentation
  `V ×_A A` along `id A`, equivalent over the base to V by projection and the
  section `(x,a(x),id)`. The successor is the existing 2-fibre product of the
  preceding augmentation and a. Thus it has p+1 factors V and includes the actual
  isomorphisms between their images in A. This harmless identity-base-change
  presentation, rather than a universe-restricting cast of V, gives a constant
  universe bound for every p. No theorem or existence choice defines the data.
- Algebraic-space representability: the first existential Z and based equivalence
  `e.toFunctor.IsEquivalence` identify the actual term with `discreteModuli Z.obj.obj`.
- The actual composite to T is `((stackAffineSourceNerve a p).2.comp h)`. The next
  two conjuncts assert its stack quasi-compactness and quasi-separatedness.
- If A is a space: existence of a based equivalence from a discrete algebraic
  space to A implies existence of a scheme W with `IsRepresentedByScheme` for the
  term. This does not assume that the given morphism a is representable.
- If A is a scheme B: for every scheme representative e of A and its structure
  map b to T, the specified `ModuliTwoIso (e.comp h) (discreteModuliMap (yoneda.map b))`
  says b is the actual transported map, not an arbitrary auxiliary map. The conclusion
  gives a scheme W representing the term by f, its actual map q to T, and a
  `ModuliTwoIso` identifying q with the transported augmentation composite.
- Separatedness over T is explicitly `IsClosedImmersion (pullback.diagonal q.left)`.
- Additional separatedness of B -> T is `IsSeparated b.left`; its consequence is
  `IsAffine W.left` for that same representing scheme. The representative is
  immaterial since both separation and affineness are invariant under isomorphism.
- Empty schemes and p=0 are allowed; there are no nonempty, Noetherian or finite-type
  hypotheses. At p=0, projection from `V ×_A A` is an equivalence even for nontrivial
  stabilizers of A, and every V -> T is separated because V is affine.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  Mathlib's `Over S`, `yoneda`, and `IsAffine` express the schemes and affine cases.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `IsRepresentedByScheme`.
  The iso-comma condition and its vertical isomorphisms were read in full.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  its sheaf/representable-diagonal/etale-atlas definition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (and its Separated import):
  `IsSeparated`, whose defining field is the closed relative diagonal.
- Proof-only imports retain the stated dependency modules for absolute change of
  base, stack qcqs permanence, space fibre products and etale smoothness, together
  with the Mathlib scheme pullback, affine-spectrum adjunction, immersion,
  properness and finite-presentation permanence material. The proof dependency
  `lem-sfb-space-qcqs-source-products` has no Lean record and therefore no module
  to import; its intended use remains in the full natural-language proof.

Source and edge checks: read Stacks `stacks-cohomology.tex`,
`lemma-general-pushforward` (076Z), the four reductions, and the current latest
blueprint direct-image proof (3). The node is an auxiliary geometric statement,
not the blueprint unit's own statement. Checked p=0, empty V and empty T (the zero
ring spectrum), non-quasi-separated S, nonseparated scheme A (e.g. doubled origin),
and A = BG_m with an affine point as source. These explain why the general
conclusion is a space, why scheme representability is conditional, and why
separation of A -> T is used only for affineness. No statement fault or dispute found.

Searches made on 2026-10-24:

- msearch.py leanfinder: "For an affine scheme V mapping to a quasi compact quasi
  separated algebraic stack over an affine scheme T, all Cech nerve terms are qcqs
  algebraic spaces; they are schemes for algebraic spaces, separated schemes for
  schemes, affine schemes for separated schemes". Eight hits: scheme affine
  transition-limit constructions, diagonal/open-cover and qcqs scheme instances;
  none states this stack nerve theorem.
- msearch.py loogle: `"Scheme", "IsSeparated", "IsAffine"`. Two hits:
  `instHasOfPostcompPropertySchemeIsAffineHomIsSeparated` and
  `Scheme.instIsSeparatedOfIsAffine`, only scheme ingredients.
- msearch.py grep: `Cech|[Aa]lgebraic[Ss]tack|[Aa]lgebraic[Ss]pace`,
  Mathlib/AlgebraicGeometry. No hits.
- rg in both lean/WeilConjectures and lean/Sheaf for the node id, stack nerve,
  iterated moduli products, and proposed declaration names; no existing theorem.
  `FibredRelativeCech` has a coefficient-specific common-universe tuple
  construction; it cannot accept a scheme source and stack in independent
  universes. No copy of it is used: the helper iterates the general, already
  existing `moduliTwoFiberProduct`. The proposed names also have no hit in
  dag/lean_names_upstream.json or Mathlib.

Validation: scompile.py compiled the file as both sandbox and library module,
without errors or unexpected warnings. The final dry-run result is recorded below.

## Second reading by Q43

A separate final reading of the node and written signature checked the clause
mapping above. No other agent was started, as required by the dispatcher brief;
this is a self-review, not a claim of an independent worker review. The maintainer's
independent review remains required. The initial output qc predicate left its test
universe arguments inferred; the final reading made both arguments explicitly t,s,
matching the input. The same reading checked the compatibility isomorphisms for
both b and q, the relative (not absolute over S) closed diagonal, the conditional
space/scheme/separated cases, and the empty and degree-zero cases. It found no
remaining hypothesis or conclusion mismatch. The full seven-step proof plan is in
the theorem docstring and every theorem proof is `sorry`.

Dry run: `deliver2.py Q43 lem-sfb-stack-affine-source-nerve-geometry --no-push`
printed `OK (dry run): commit e37a6ad4fb2 passes the preflight and compiles; nothing pushed`.
