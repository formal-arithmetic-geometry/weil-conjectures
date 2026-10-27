## Worker report

The module `Sheaf.Algebra.Homology.TorOneExtensionExactness` states
`CategoryTheory.tor_one_extension_exact`, with its proof deliberately `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement changes.
The item node is copied without changes except its `lean` record.

The correspondence with the node is as follows:

| Node clause | Lean rendering |
| --- | --- |
| R is a commutative ring | `{R : Type r} [CommRing R]` |
| A, B, C, M are R-modules | Independent `Type a`, `Type b`, `Type c`, `Type m` binders, each with `AddCommGroup` and `Module R` instances |
| u and v are R-linear | `f : A →ₗ[R] B`, `g : B →ₗ[R] C` |
| 0 → A → B → C → 0 is short exact | `hf : Function.Injective f`, `hfg : Function.Exact f g`, `hg : Function.Surjective g`, the module convention in the exact-sequence node's `lean.note` |
| Tor in degree one | `Tor' ... 1`, deriving tensor in the first variable exactly as recorded by `def-weil-pbc-tor-modules` |
| Tor_1(u,M) | `((Tor' ... 1).map (ModuleCat.ofHom ...)).app (ModuleCat.of ... M)` with f transported canonically as explained below |
| Tor_1(v,M) | The same expression with g |
| Kernel equals image at the middle Tor module | `Function.Exact` of the underlying linear maps (`.hom`); `LinearMap.exact_iff` identifies this with `ker second = range first` |
| No flatness, finiteness or Noetherian assumptions | No such hypotheses or instances occur |

Size transport: Mathlib's `ModuleCat.monoidalCategory` in
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic` fixes the module universe to
the ring universe (the file documents this restriction). To cover independently
sized rings and all four independently sized modules, the statement computes Tor
in `ModuleCat (ULift.{max r a b c m} R)`, on the corresponding `ULift` modules.
The lifted ring is canonically ring-isomorphic to R. Its action is through
`ULift.down`, and the lifted modules are canonically linearly equivalent to the
original modules with this action. For example the map lifting f is exactly
`ULift.moduleEquiv.symm.toLinearMap.comp
  ((f.restrictScalars (ULift R)).comp ULift.moduleEquiv.toLinearMap)`, with all
universes explicit in the actual statement. Thus it sends `ULift.up x` to
`ULift.up (f x)`; the second map similarly lifts g. This is coefficient and
universe transport of the specified Tor functor, not an arbitrary map or a new
notion. There is no equality assumption on universes and no hidden typeclass
assumption on the mathematical objects. The original hypotheses apply before
transport, so the statement also handles modules of different sizes.

Dependency declarations read and used:

- `def-weil-pbc-exact-sequence`: `Mathlib.Algebra.Homology.ExactSequence`,
  `CategoryTheory.ComposableArrows.Exact`; also read
  `CategoryTheory.ShortComplex.Exact` and `CategoryTheory.ShortComplex.ShortExact`.
  The node explicitly prescribes `Injective` / `Function.Exact` / `Surjective`
  for modules with independent universes. `Mathlib.Algebra.Exact.Basic`,
  `LinearMap.exact_iff`, gives the kernel-image equivalence.
- `def-weil-pbc-tor-modules`: `Mathlib.CategoryTheory.Monoidal.Tor`,
  `CategoryTheory.Tor'`, including its full definition and its docstring.
- Proof dependency `lem-weil-pbc-free-resolution-ses-split`:
  `WeilConjectures.Algebra.Homology.FreeResolutionSesSplit`,
  `Module.exists_free_resolution_ses_split`, read its full signature and proof plan.
- Proof dependency `lem-weil-pbc-ring-modules-grothendieck-abelian`:
  `Mathlib.Algebra.Category.ModuleCat.AB`, the `IsGrothendieckAbelian` instance.
- Proof dependency `lem-weil-pbc-complex-ses-homology-long-exact`:
  `Mathlib.Algebra.Homology.HomologySequence`,
  `CategoryTheory.ShortComplex.ShortExact.homology_exact₂`, together with
  `homology_exact₁`, `homology_exact₃`, and the connecting morphism `δ`.
- Proof dependency `lem-weil-pbc-tor-map-via-resolution-lift`:
  `Mathlib.CategoryTheory.Abelian.LeftDerived`,
  `CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality` and
  `CategoryTheory.ProjectiveResolution.leftDerived_app_eq`; read their full
  signatures and the canonical `isoLeftDerivedObj` construction.

The module includes the recorded proof dependencies as plain imports and the
statement dependencies as public imports. Every variable and universe is bound;
`set_option autoImplicit false` enforces this. The theorem docstring contains all
four steps of the accepted proof, with the named DAG dependencies and sources.

Source check: read `literature/stacks-project/algebra.tex`,
`lemma-long-exact-sequence-tor` (Tag 00M0), whose long exact sequence contains the
three Tor-one terms. The node exchanges the arguments, legitimate for a
commutative ring; its accepted proof instead derives directly in the first
variable, so the formal statement does not require a separate Tor-symmetry API.

Edge cases checked before writing:

- The zero ring and the zero coefficient module M give only zero Tor modules.
- A = 0 or C = 0 makes the relevant remaining map an isomorphism; exactness has
  the expected meaning, with no added nonzero condition.
- For `0 → Z/2 → Z/4 → Z/2 → 0` and `M = Z/2`, Tor-one of the first map is an
  isomorphism and Tor-one of the second map is zero, so the image is exactly the
  kernel despite nonflat M. This is an essential nonsplit test case.
- Over a field the Tor-one modules vanish, and the statement still applies.
- A, B, C and M can live in different universes, including ones smaller or
  larger than R; the explicit maximum and canonical coefficient lift cover all.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “The first Tor functor sends a short exact
  sequence A B C to an exact sequence Tor1 A M to Tor1 B M to Tor1 C M”. Eight
  hits, including `ShortComplex.SnakeInput.L₁'_exact`, `L₁_exact`, `L₀'_exact`,
  `L₂'_exact`, `L₀_exact`, Ext exactness and `SnakeLemma.δ_aux`; none is the
  specified Tor segment.
- `msearch.py ... leansearch`: the same query. Eight hits: `Tor`, `Tor'`,
  `Functor.IsHomological.exact`, `Tor_obj`, snake-input declarations and
  `Rep.Tor`; definitions and general homological exactness, not this statement.
- `msearch.py ... loogle`:
  `CategoryTheory.Functor.leftDerived, CategoryTheory.ShortComplex.Exact`.
  No hits. An earlier incorrectly escaped apostrophe query was rejected as
  unknown identifier `x27`; no conclusion is drawn from that attempt.
- `msearch.py ... grep`: `Tor.*exact|exact.*Tor` in `CategoryTheory/Monoidal`.
  Twenty broad matches in unrelated files; inconclusive by itself. Read the
  entire actual `Mathlib/CategoryTheory/Monoidal/Tor.lean`: definitions and
  projective vanishing only, with no exactness theorem.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `Tor.*exact|exact.*Tor`, then narrowed to `tor_one|torOne|TorOne` in the algebra
  files. The nearby existing theorem is
  `CategoryTheory.tor_long_exact_first_variable` in
  `WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable`. Read its full
  signature and docstring: it starts with `Tor_1(B,M) → Tor_1(C,M) → A ⊗ M` and
  gives exactness at `Tor_1(C,M)`, not at `Tor_1(B,M)`. It therefore cannot serve
  as an existing declaration for this node. Other hits are flatness, Tor
  vanishing, and geometric Tor-amplitude statements.
- The item id has no upstream source occurrence; the proposed declaration name
  has no occurrence in `dag/lean_names_upstream.json`, Mathlib's Tor file, or
  either project source tree.

No disputed statement or node fault was found. The sole postponed theorem is
`CategoryTheory.tor_one_extension_exact`, owned by this DAG node. Validation uses
only `scompile.py` and `deliver2.py`, never a local or global library build.

## Second reading by Q35

I reread the completed signature against the unchanged node and the source after
writing it. This is a second pass by the same dispatcher worker; the independent
review is the maintainer's, as specified in the assignment. No other agents were
started. The four object binders, two linear maps, three short-exact hypotheses,
degree one, fixed second argument, and exactly one middle-exactness conclusion
match the node. In particular the functor uses `.map ... .app ...`, so it varies
the first argument, rather than `.obj ... .map ...` which would vary the second.
The two occurrences of the lifted B have identical types and actions. The
transported maps are conjugates of the given maps, and `Function.Exact` states
both inclusions of kernel and image. The first compiler check exposed Mathlib's
same-universe ring requirement; lifting the ring too repaired this without
restricting the theorem. No additional mathematical hypotheses were introduced.
