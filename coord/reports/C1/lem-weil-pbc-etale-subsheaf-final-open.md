## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSubsheafFinalOpen` states
`AlgebraicGeometry.Scheme.existsUnique_open_of_etale_subsheaf_final`, with a `sorry`
proof. No definition, dependency replacement, new node, or statement correction is needed.
The declaration docstring carries the three proof steps of the node. The source was
read at https://stacks.math.columbia.edu/tag/04HV because the local Stacks checkout is
absent: Lemma 59.31.1 identifies a subsheaf of the final étale sheaf with a unique open
subscheme; its proof constructs the union of étale images with nonempty sections.
The stalk clause is the node's consequence of this representation and the recorded
pointed-neighbourhood colimit definition.

Hypotheses and clauses, individually:

- A scheme S: `(S : Scheme.{u})`.
- A sheaf of sets on the small étale site: `(H : Sheaf S.smallEtaleTopology
  (Type (max u v)))`, using Mathlib's sheaf condition, not a private copy.
- A subsheaf of the final sheaf: `hH : ∀ U : S.Etale,
  Subsingleton (H.obj.obj (op U))`. This is an equivalent formulation of the
  hypothesis, rather than extra structure or a weakening. For a sheaf of sets,
  the unique natural map to the singleton sheaf is componentwise injective
  precisely when each section set is subsingleton. Such a map is a monomorphism
  of sheaves; conversely a subsheaf inclusion is injective on sections.
- Existence and uniqueness of the open subscheme W: `∃! W : S.Opens, ...`.
  `W.toScheme` is the restriction of S to W and `W.ι` is its open immersion.
  Opens are used so uniqueness is literal, rather than equality of arbitrary
  isomorphic presentations of an open immersion.
- Every étale morphism U → S: `∀ U : S.Etale`; `U.left` is its source and
  `U.hom` is the structure morphism. No affine, finite, nonempty, or
  quasi-compact restriction is imposed.
- The section set is singleton exactly when the morphism factors through W:
  `Nonempty (Unique (H.obj.obj (op U))) ↔
  ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom`.
  `Unique A` is data, so its existence is expressed by `Nonempty (Unique A)`.
- Empty otherwise: negation of the same factorization proposition implies
  `IsEmpty (H.obj.obj (op U))`. This is explicitly included, even though it
  follows from the singleton equivalence and `hH`.
- Every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ S)`. This uses exactly the geometric-point dependency's
  specialization, without replacing algebraically closed by separably closed.
- The point lies in W exactly when its stalk is nonempty:
  `x default ∈ W ↔ Nonempty ((pointSmallEtale x).sheafFiber.obj H)`.
  `default` is the unique point of Spec Ω, so `x default` is the underlying
  image point (also described by `Scheme.SpecToEquivOfField`).
- Equivalently a singleton stalk: `Nonempty ((pointSmallEtale x).sheafFiber.obj H)
  ↔ Nonempty (Unique ((pointSmallEtale x).sheafFiber.obj H))`.
  Both stalk clauses concern the same W and the same H, not a chosen substitute.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and `Scheme.Opens`
  in `Mathlib.AlgebraicGeometry.Scheme`; `Scheme.Opens.toScheme` and `.ι` in
  `Mathlib.AlgebraicGeometry.Restrict` provide the open subscheme and inclusion.
- `def-weil-pbc-etale-sheaf-of-sets`: `CategoryTheory.Sheaf` in
  `Mathlib.CategoryTheory.Sites.Sheaf`, specialized to
  `Scheme.smallEtaleTopology` in `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `def-weil-geometric-point`: `[Field Ω] [IsAlgClosed Ω]` and a map
  `Spec (.of Ω) ⟶ S`, exactly as its `mathlib_match.how` specifies.
  Read `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`
  and `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic`; no bundled
  geometric-point definition is introduced.
- `def-weil-pbc-geometric-stalks`: `Scheme.pointSmallEtale` in
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
  `GrothendieckTopology.Point.sheafFiber` in
  `Mathlib.CategoryTheory.Sites.Point.Basic`. Read their signatures and
  definitions: the fiber uses lifts over x, and the sheaf fiber restricts
  the colimit of the presheaf over the opposite category of elements.

All dependencies are available through the one used import
`Mathlib.AlgebraicGeometry.Sites.EtalePoint`. No dependency's recorded notion
needed replacing.

Edge cases checked before writing:

- Empty S: its only open is the empty open, and there are no geometric points;
  the empty étale object has a singleton section set by the empty-cover sheaf
  condition, as required by its unique factorization through the empty open.
- W empty with S nonempty: an étale object factors through it precisely when
  its source is empty; only that object has singleton sections. Geometric
  stalks are empty. This also explains why the constantly empty presheaf is
  not a counterexample: it fails the sheaf condition on the empty object.
- W all of S: the final sheaf has singleton sections everywhere, every
  morphism factors, and every geometric stalk is singleton.
- Nonempty objects not mapping entirely into W: sections are empty even if
  part of their image meets W. The explicit factorization equation captures
  the whole-image condition, not just an intersection or a point condition.
- Universe binders u and v are explicit, with no auto-implicit parameters.
  Sets live in `Type (max u v)` so the u-small stalk colimits exist, while v
  remains arbitrary. For subterminal sheaves this imposes no cardinality
  restriction: all values have at most one element and any such sheaf can
  be resized into this universe. Fields and schemes use the same universe
  as the dependency's recorded `pointSmallEtale` and `SpecToEquivOfField`.

Searches for an existing statement (via `/home/ubuntu/weil-launcher/msearch.py`
with group C1 and this item):

- Lean Finder, query: `A subsheaf of the terminal sheaf on the small etale site
  of a scheme is represented by a unique open subscheme`. Eight hits include
  `Scheme.Opens`, `Scheme.Opens.exists_toScheme`, `Scheme.smallEtaleTopology`,
  and `Scheme.Etale`; none states the representation of subterminal sheaves.
- Loogle, query: `AlgebraicGeometry.Scheme.Opens, CategoryTheory.Sheaf`.
  Two hits: `Scheme.AffineZariskiSite.sheafEquiv` and
  `Scheme.Modules.sheafComposePushforwardComp`; neither is the statement.
- Mathlib grep, query: `subterminal|subsheaf.*final|subsheaf.*terminal`.
  Eight hits concern `CategoryTheory.Subterminal` and exponential ideals;
  no scheme-level representation theorem.
- LeanSearch, query: `subterminal sheaf on etale site represented by open
  subscheme`. Service unavailable (Internal Server Error), recorded as
  unavailable rather than as evidence of no match.
- `rg -n 'subterminal|subsheaf.*final|subsheaf.*terminal|
  lem-weil-pbc-etale-subsheaf-final-open'` on the source `WeilConjectures`
  and the project `lean/Sheaf`: no matching declaration.
- `rg -n 'existsUnique_open_of_etale_subsheaf_final'` on Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no name collision.

Validation: `scompile.py C1 lem-weil-pbc-etale-subsheaf-final-open` on the module
returned exit code 0, compiled in 1.7 seconds, with no errors or warnings.
No statement dispute or node fault was found.

## Second reading by C1

I reread the node statement, its Stacks source (Tag 04HV, `lemma-support-subsheaf-final`, used in Tag 09XM), and the complete Lean declaration. The correspondence is as follows.

- The node's scheme `S` is the explicit `(S : Scheme.{u})`; the Lean `Scheme` is the dependency declaration `AlgebraicGeometry.Scheme`.
- The node's sheaf `H` on the small étale site is `H : Sheaf S.smallEtaleTopology (Type (max u v))`, using the recorded Mathlib sheaf notion.
- “Subsheaf of the final sheaf” is rendered by `hH : ∀ U : S.Etale, Subsingleton (H.obj.obj (op U))`. For sheaves of sets this is exactly the componentwise subterminal condition, with the canonical map to the terminal sheaf; it adds no geometric or finiteness assumption.
- The unique open subscheme is `∃! W : S.Opens`; `W.toScheme` and `W.ι` are the recorded restriction and open immersion, so uniqueness is literal equality of opens.
- The universal étale-object clause is `∀ U : S.Etale`. The factorization condition is exactly `∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom`.
- “Singleton exactly when factoring” is the displayed equivalence `Nonempty (Unique (H.obj.obj (op U))) ↔ ...`; the separate implication from failure of factorization to `IsEmpty (H.obj.obj (op U))` records the node's “empty otherwise” clause. No affine, quasi-compact, nonempty, or separated restriction was introduced.
- A geometric point is exactly `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)`, matching the dependency's algebraically closed field specialization.
- The support criterion is `x default ∈ W ↔ Nonempty ((pointSmallEtale x).sheafFiber.obj H)`, using the recorded geometric stalk declaration. The parenthesized equivalence to a singleton stalk is the second displayed equivalence with `Nonempty (Unique ...)`.

The proof docstring follows all three node proof steps: union of étale images and openness; local pullback sections, sheaf gluing and uniqueness; then uniqueness of the open and the pointed-stalk criterion. The declaration has no free variables because `u`, `v`, `S`, `H`, and `hH` are all explicit. The empty scheme, empty open, empty étale object, full open, zero/nonempty section sets, `n=0` (irrelevant here), and the absence of geometric points over an empty scheme were checked; no edge case is excluded by the universe binders. In particular, the explicit factorization equation requires the whole image to lie in `W`, as in the source.

I searched the DAG, Mathlib, `WeilConjectures`, and `lean/Sheaf` for subterminal/final-sheaf-on-étale-site representations and for the declaration name; no existing statement or definition matches. Lean Finder, Loogle, grep, and the recorded unavailable LeanSearch query likewise found no match. The dependency declarations (`Scheme`, small étale sheaves, geometric points, and `sheafFiber`) were checked against their signatures; no dependency module was unusable and no mismatch was found. Therefore no repair to the worker's Lean or node statement was needed. The module compiles cleanly with `scompile.py`; only the theorem proof remains `sorry`, as required for stage 2.

## Reviewer fix (R-esf1003)

The subsheaf hypothesis `hH : ∀ U : S.Etale, Subsingleton (H.obj.obj (op U))` was replaced by
`[Mono (terminal.from H)]`: the node's "subsheaf of the final sheaf" is stated as a monomorphism
into the terminal sheaf `⊤_ (Sheaf S.smallEtaleTopology (Type (max u v)))`, the project's
`Mono`/terminal form of subsheaves, rather than an unrecorded section-wise reformulation
(equivalent, but a second form of the notion). `open ... Limits` added. All other clauses unchanged.
