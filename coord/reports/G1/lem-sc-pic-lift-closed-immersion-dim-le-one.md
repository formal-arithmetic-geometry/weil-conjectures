## Worker report

The module `lean/Sheaf/AlgebraicGeometry/PicardLift.lean` states the lifting lemma from
Stacks Project, Varieties, Lemma 09NY. It uses the existing scheme structure, Mathlib's
closed immersion predicate, the topological Noetherian-space predicate, the Mathlib
Krull dimension `topologicalKrullDim`, the landed invertibility class, and the landed
tensor pullback functor.

The hypotheses and conclusion are rendered as follows. The scheme objects are
`{X Z : Scheme.{u}}`. The hypothesis that the underlying topological space of `X` is
Noetherian is the typeclass `[NoetherianSpace X]`. The closed immersion `i : Z ⟶ X`
and its property `[IsClosedImmersion i]` render the morphism and closed-immersion
hypothesis. The dimension hypothesis `dim X ≤ 1` is
`(hdim : topologicalKrullDim X ≤ 1)`. For each module, the phrase “for every invertible
`O_Z`-module `N`” is `∀ (N : Z.Modules), N.IsInvertible →`. The asserted lift is
`∃ (L : X.Modules), L.IsInvertible ∧ Nonempty ((tensorPullback i).obj L ≅ N)`, which
renders an invertible module on `X` and an isomorphism from its pullback to `N`.
The final sentence of the node, identifying this with surjectivity on Picard groups,
is the explanatory reformulation of this existence statement and introduces no
additional Lean hypothesis or conclusion.

Dependency declarations used are `AlgebraicGeometry.Scheme` (Mathlib),
`topologicalKrullDim` (Mathlib, `Mathlib.Topology.KrullDimension`),
`AlgebraicGeometry.IsClosedImmersion` (Mathlib,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`),
`AlgebraicGeometry.Scheme.Modules.IsInvertible`
(`WeilConjectures.AlgebraicGeometry.Modules.Invertible`), and
`AlgebraicGeometry.Scheme.Modules.tensorPullback`
(`Sheaf.AlgebraicGeometry.TensorPullback`).

Edge cases checked against the statement are: `Z = X` with `i` the identity (the
conclusion asks for an invertible module isomorphic to the original one), empty `Z`
(the unique module is covered by the universal quantifier), zero-dimensional `X`, and
empty `X` (where the dimension bound and the Noetherian typeclass remain meaningful).
No edge case is excluded by the Lean statement.

Searches for an existing declaration were made with `msearch.py G1 ... leanfinder` for
“Picard group of scheme surjects onto Picard group of closed subscheme when dimension
at most one”, returning only unrelated affine/ring results; with `msearch.py ... loogle`
for `"Pic", AlgebraicGeometry.Scheme`, returning no scheme Picard declaration; with
`msearch.py ... grep` for `Pic|Picard` in Mathlib AlgebraicGeometry, finding only ring
Picard comments; and with `rg -n "Pic|IsInvertible|tensorPullback"` in the project,
which found only the dependency declarations and no lifting theorem. Thus no existing
project or Mathlib declaration has this statement.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

I reread the node and the module side by side. The Noetherian hypothesis is rendered
by `[NoetherianSpace X]`, the dimension bound by `topologicalKrullDim X ≤ 1`, and the
closed immersion by `i` with `[IsClosedImmersion i]`. The universal quantifier binds
exactly an arbitrary `N : Z.Modules` and its invertibility proof. The conclusion binds
exactly an `L : X.Modules`, requires `L.IsInvertible`, and states the required
isomorphism `((tensorPullback i).obj L ≅ N)`. The module uses the recorded pullback
declaration rather than a private copy. The node's Picard-surjectivity wording is
faithfully represented by the existence conclusion. I found no mismatch and made no
changes during this reading.


## Second reading by G1

Independently opened the sandbox node and PicardLift.lean, all five statement-dependency
nodes, the source signatures of Scheme, Modules, IsClosedImmersion, topologicalKrullDim,
NoetherianSpace and IsInvertible, and the landed TensorPullback module. Read Stacks
varieties.tex on the server, including the chapter notation, the section introduction
and Lemma 09NY with its proof (label lemma-lift-line-bundle-from-reduction-dimension-1).
09NY is about arbitrary schemes, not necessarily schemes over a field, separated schemes
or schemes with Noetherian local rings. The chapter's notation for a ground field adds
no hypothesis to this lemma, which does not mention that field.

Object/hypothesis/conclusion checklist:

- Ambient scheme X and closed subscheme Z: `{X Z : Scheme.{u}}`, the recorded Mathlib
  scheme category. Exact; neither object is assumed reduced, nonempty, affine or separated.
- Noetherian underlying space of X: `[NoetherianSpace X]`. Exact. Mathlib defines this
  as well-founded strict inclusion in the opposite direction on opens; its
  `noetherianSpace_TFAE` identifies it with well-founded strict inclusion on closed
  subsets, hence precisely the node's minimal-closed-subset condition. This does not
  impose the stronger algebraic `IsNoetherian X` condition.
- Dimension at most one: `(hdim : topologicalKrullDim X ≤ 1)`. Exact; the definition
  is `krullDim (IrreducibleCloseds X)` valued in `WithBot ℕ∞`, matching nonempty
  irreducible closed chains and the empty-space convention of the dependency node.
- Closed immersion i: `(i : Z ⟶ X) [IsClosedImmersion i]`. Exact; the class consists
  of a closed embedding and surjective stalk maps, equivalently the source's
  surjection of sheaves. No ideal-sheaf finiteness hypothesis is added.
- Arbitrary invertible O_Z-module N: `∀ (N : Z.Modules), N.IsInvertible →`. Exact;
  `Modules` is the category of sheaves of modules, and `IsInvertible.exists_isoUnit`
  is local isomorphism with the structure sheaf. Such a module is locally free of
  rank one and thus quasi-coherent; no extra quasi-coherence assumption is needed.
  The recorded upstream notion uses restriction via `pullback U.ι` on open subsets.
- Existence of an invertible O_X-module L: `∃ (L : X.Modules), L.IsInvertible ∧`.
  Exact, in the prescribed order after quantifying over N and its invertibility.
- Pullback is isomorphic to N as O_Z-modules:
  `Nonempty ((tensorPullback i).obj L ≅ N)`. Exact; the recorded landed functor
  explicitly forms the inverse-image module and changes scalars along
  `i⁻¹ O_X → O_Z`, giving the sheafified tensor formula in def-pc-module-pullback.
  The isomorphism is in Z.Modules, not merely an isomorphism of underlying groups.
- Picard restriction is surjective: this is exactly the preceding existence statement
  on isomorphism classes, not an additional clause requiring a separate group object.

Edge cases: identity immersion allows L=N up to canonical pullback isomorphism;
empty Z and empty X are allowed without Nonempty assumptions. Empty X has dimension
bottom, hence satisfies the bound. Dimension zero is included, as is arbitrary
characteristic and arbitrary commutative local rings (no field binder). There is no
index set or exponent n in this statement. On a nonempty scheme the zero module is
not invertible and is excluded only by the intended hypothesis; on the empty scheme
invertibility is vacuous and the module category has its unique isomorphism class.
The universe u is arbitrary, with both schemes and their modules in the recorded
scheme-module universe; any pair of differently sized schemes may be placed in a
common larger universe. Invertible modules are locally structure-sheaf-sized, so
this convention does not lose Picard classes. Every variable and universe is bound.

Independent searches used different wording from the worker: msearch leanfinder
"extend a locally free rank one sheaf from a closed subscheme of a topologically
noetherian scheme of Krull dimension one" returned eight unrelated section/localization
results; loogle `"IsInvertible", "IsClosedImmersion"` returned no hits. LeanSearch
"line bundles extend from any closed subscheme of a noetherian topological scheme of
dimension at most one" was unavailable (Internal Server Error), recorded without
claiming a negative verdict. msearch grep `line.bundle|extend.*invertible|lift.*invertible|
isInvertible.*isClosedImmersion` in Mathlib AlgebraicGeometry returned no hits. Direct
rg in WeilConjectures and lean/Sheaf for lifting/extending bundles or invertible modules
found blowup ideal results and the ample-sheaf proof's citation of this item, not a
second declaration. The proposed full theorem name is absent from both source trees.
Therefore existing:true would not be appropriate.

No new nodes or dependency modules occur in this delivery. No statement_change occurs;
no citer verdicts need rechecking. All five recorded dependencies are usable and their
notions are used without private copies. No definition is introduced or hollow; the
only theorem proof is sorry. The module and declaration docstrings cite 09NY and the
item's blueprint id. The previous proof paragraph compressed the four steps and
omitted dependency names: expanded it to state the exact units sequence, degree-two
vanishing, degree-one comparison, Hilbert-90 identification and pullback compatibility,
with all proof-dependency ids. No mathematical mismatch was found and the signature
and node lean.statement remain unchanged and verbatim equal. Imports, namespace,
100-character line limit and explicit universe were checked.
