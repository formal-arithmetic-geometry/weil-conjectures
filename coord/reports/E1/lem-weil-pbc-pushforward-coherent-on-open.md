## Worker report

The module `Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen` states
`AlgebraicGeometry.Scheme.Modules.pushforward_coherent_on_open`, with only a `sorry` proof.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypotheses and clauses, individually matched:

- Scheme X: `(X : Scheme.{u})`, without Noetherian or separation assumptions.
- Inclusion of an open subscheme: `(U : X.Opens)` and Mathlib's canonical `U.ι`.
- Ambient closed subset T: `(T : TopologicalSpace.Closeds X)`.
- T contained in U: `hT : (T : Set X) ⊆ (U : Set X)`.
- O_U-module F: `(F : U.toScheme.Modules)`.
- F coherent: `hF : RingedSpace.IsCoherent U.toScheme.toRingedSpace F`.
- Support of F contained in T: `hSupp` says the nonzero-stalk locus
  `{x : U.toScheme | ¬ Subsingleton (F.presheaf.stalk x)}` is contained in
  `U.ι.base ⁻¹' (T : Set X)`. Taking the inverse image identifies ambient T with its subset
  of U; this adds no assumption and uses the project's inline support convention.
- j_* F coherent: `RingedSpace.IsCoherent X.toRingedSpace ((pushforward U.ι).obj F)`.
- Restriction back to U equals F: `Nonempty ((restrictFunctor U.ι).obj
  ((pushforward U.ι).obj F) ≅ F)`. The categorical equality is an isomorphism of O_U-modules,
  consistent with the node's reference to `restrictFunctorAdjCounitIso`.
- Restriction to X minus T is zero: `IsZero ((restrictFunctor (Scheme.Opens.ι T.compl)).obj
  ((pushforward U.ι).obj F))`. `T.compl` is the bundled open complementary to T.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`, full definition
  finite type plus finite-type kernels for all maps from finite free modules on opens.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`: the support convention in
  `AlgebraicGeometry.Scheme.Modules.HasSupportProperOver` is used inline, exactly as instructed
  by STATE/brief-stage2. Properness is not asserted or used by this node, so this module is
  not imported merely to carry the support formula.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` and `Scheme.Opens`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `tensorPullback` and its adjunction statement were
  read. The item needs only its right adjoint, Mathlib's `Scheme.Modules.pushforward`, and
  does not use or duplicate tensor pullback, so this module need not be imported.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.pushforward`, `restrictFunctor`,
  `restrictFunctorAdjCounitIso`, `restrictAdjunction`, and the left-adjoint instance, read in
  full; this is the mathlib_match of the restriction dependency. The quasi-coherence instance
  `Scheme.Modules.isQuasicoherent_restrictFunctor` was also read in Modules/Tilde.lean, but
  quasi-coherence is not a separate clause of the present item.
- `Mathlib.Topology.Sets.Closeds`: `TopologicalSpace.Closeds.compl`.

Edge cases checked before writing: U empty forces T empty and F the zero sheaf, so all three
conclusions hold; T empty forces every stalk of F to vanish and hence F vanishes; U = X
reduces the first restriction to the identity; T = X forces U = X and gives restriction to
an empty complementary open. The zero module is allowed, including on arbitrary non-Noetherian
schemes. No properness, quasi-compactness, or nonemptiness assumption is introduced.
All variables and the single universe u are explicit; modules use the project's carrier.

Source: the local Stacks checkout is absent. Opened https://stacks.math.columbia.edu/tag/0CYJ
and read Lemma 30.9.11 and its proof. It states exactly these hypotheses without a locally
Noetherian assumption, and uses the same two-open-cover argument. The declaration docstring
contains all four proof steps of the DAG, including the named proof dependencies.

Searches for an existing statement (msearch.py with group E1 and this item):

- LeanFinder: "Pushforward of a coherent module from an open subscheme whose support is closed
  in the ambient scheme is coherent". Eight hits: pushforward, its section formula, restriction,
  the sheaf property, and ideal-sheaf support results; no coherent-pushforward theorem.
- Loogle: "Scheme.Modules.pushforward, Scheme.Modules.restrictFunctor". No hits;
  unknown identifier `Scheme.Modules.pushforward` in the search service.
- LeanSearch: "coherent pushforward open immersion closed support". Service unavailable:
  Internal Server Error. Recorded as unavailable, with no mathematical verdict.
- Mathlib grep: "coherent|Coherent" under AlgebraicGeometry/Modules. Five hits in Tilde.lean
  concerning quasi-coherence; none is this statement.
- rg in WeilConjectures and lean/Sheaf: "coherent.*[Pp]ushforward|[Pp]ushforward.*[Cc]oherent|
  lem-weil-pbc-pushforward-coherent-on-open". Finite-pushforward and closed-immersion results,
  comments, and proof references; no existing open-immersion closed-support statement.
- The same search included dag/lean_names_upstream.json; only quasi-coherent pushforward
  names for affine and closed morphisms were found. Literal item-id search of upstream sources
  found no declaration for this item.

No node fault or disputed statement was found. Server compile and delivery dry-run results
are recorded below after validation.

Validation: server scompile.py completed with exit code 0 in 1.7 seconds, with no errors or
warnings. The complement inclusion is explicitly `Scheme.Opens.ι T.compl` because dot notation
on the topological `Closeds.compl` does not resolve the scheme inclusion. No change of meaning.

Delivery validation: deliver2.py --no-push printed OK: the module compiles and passes preflight,
except for the independent second-reading section which the second reader must supply.
Nothing was pushed; no second-reading section was written by this worker.


## Second reading by E1

I independently opened the node, its source, the declaration, all five statement
 dependencies, and the definitions used by those dependencies. Verdict: the Lean
says exactly what the node says. No Lean or node changes were required.

Object/hypothesis/conclusion checklist (all PASS):

- Ambient scheme X is `(X : Scheme.{u})`; no finiteness, separation, field, or
  Noetherian instance is added.
- Open subscheme U and its inclusion j are `(U : X.Opens)` and `U.ι`.
  This canonical inclusion covers precisely the inclusion required by the node.
- Closed ambient subset T is `(T : Closeds X)`; `hT` is exactly T contained in U.
- The O_U-module is `(F : U.toScheme.Modules)`, Mathlib's sheaf-of-modules category.
- Coherence is `hF : RingedSpace.IsCoherent U.toScheme.toRingedSpace F`.
  I read Coherent.lean: finite type and finite-type kernels of every finite-free
  map on every open, with n including zero. This is full coherence, not merely
  finite presentation or coherence on Noetherian schemes.
- Support containment is `hSupp`, the nonzero-stalk locus contained in the inverse
  image of ambient T under `U.ι.base`. Subsingleton for the module stalk means the
  zero module. ClosedSubsetProperOverBase.lean uses precisely this support notion;
  its properness and locally-finite-type clauses are not hypotheses here.
- Direct image is `((pushforward U.ι).obj F)`. I read TensorPullback.lean's
  adjunction: its right adjoint is this same Mathlib pushforward, not another
  direct image. Tensor pullback itself is not used by the item.
- The first conclusion is its coherence on X, using the same IsCoherent predicate.
- The second conclusion is `Nonempty ((restrictFunctor U.ι).obj
  ((pushforward U.ι).obj F) ≅ F)`. Equality in the node is equality up to the
  canonical module isomorphism, explicitly identified in its proof step 1.
- The third conclusion is `IsZero` of restriction to `Scheme.Opens.ι T.compl`.
  This is zero in the module category on the open complement, not vanishing of
  global sections alone. All conclusions concern the same direct image.

The restriction dependency has no lean record, but its mathlib_match explicitly
lists restrictFunctor, restrictAdjunction, its IsLeftAdjoint instance, and
isQuasicoherent_restrictFunctor. I opened Sheaf.lean (restriction definition,
section and map formulas, counit iso and adjunction) and Tilde.lean (quasi-coherent
restriction instance). These give the dependency as stated; no dependency module
or new definition is needed. The scheme dependency is Mathlib Scheme, with the
usual open subschemes, and all carriers agree with the recorded dependencies.

The local Stacks .tex checkout is absent. I independently opened
https://stacks.math.columbia.edu/tag/0CYJ and the surrounding section
https://stacks.math.columbia.edu/tag/01XY. The section intro discusses a locally
Noetherian convention, but 0CYJ expressly introduces an arbitrary scheme, unlike
its preceding lemmas which expressly assume locally Noetherian. Its proof uses
only restriction, zero modules, and locality of coherence, valid on arbitrary
ringed spaces. Thus the node and Lean correctly retain the lemma's explicit
arbitrary-scheme statement; a Noetherian hypothesis would strengthen it.

Edge cases: empty X, empty U (then hT forces empty T), empty T (then hSupp
forces zero stalks), U equal to X, T equal to X (then U equals X), and zero F
are all included. There is no index set, cohomology degree, field, or
characteristic parameter. The universe u is explicit and unrestricted, and
matches the project's scheme/module carrier; no smallness or nonemptiness
hypothesis is imposed. All variables are bound.

Independent searches, using different wording from the first worker:

- LeanFinder via msearch: `coherent sheaf direct image open subset closed support
  extension by zero`: eight hits, including restriction sections/maps and
  ringed-space zero restriction; no theorem about coherent direct image with
  closed ambient support.
- Loogle via msearch: `"pushforward", "coherent"`: five quasi-coherent-data
  pushforward hits. These do not assert coherence or closed-support direct image.
- rg in Mathlib AlgebraicGeometry, upstream WeilConjectures and project Sheaf:
  coherent near direct image, pushforward, or closed support. Read the relevant
  finite and closed-immersion results: their morphism/Noetherian hypotheses differ.
  No duplicate of this arbitrary-open closed-support theorem was found.

H5/H6/H8/H9 checks: the module introduces no definitions or private copies,
contains exactly the named statement with sorry, and proves nothing. Both
source docstrings carry the blueprint id. The theorem docstring carries all
four node proof steps and their dependencies. Imports are used, names are
upstream-compatible, and lines meet the 100-character limit.

Mismatches found: none in the delivered Lean or node. An exploratory dependency
skeleton was removed after opening the dependency's existing Mathlib match;
it is not part of the delivery. Only this second-reading report was added.
The node lean.statement is verbatim equal to the theorem signature.
Independent server compilation of the delivered file exited 0 in 1.7 seconds,
without errors or warnings.
