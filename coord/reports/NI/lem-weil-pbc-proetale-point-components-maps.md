## Worker report

The module states `AlgebraicGeometry.ProEtale.proEtale_point_components_maps`, with one
postponed theorem and no definitions. The node is unchanged except for its Lean record.

Hypothesis and clause correspondence:

- Any scheme X is `(X : Scheme.{u})`; no quasi-compactness assumption on X is imposed.
- An object U of the small pro-etale site is `(U : X.ProEt)`, with the topology
  `Scheme.ProEt.topology X`. Its underlying scheme is `U.left`.
- Affineness is `IsAffine U.left`, supplied as a proposition argument, without choosing
  any extra affine presentation.
- Weak contractibility is the explicit quantification over `F G : Sheaf
  (Scheme.ProEt.topology X) (Type (u + 1))` and `f : F ⟶ G`, requiring
  `Epi f → Function.Surjective (f.hom.app (op U))`. The larger sheaf-value universe
  follows the small-site size convention; site object and morphism universes are not equated.
- The connected-component quotient with its quotient topology is Mathlib's
  `ConnectedComponents U.left`, not a discrete replacement. Its profiniteness is the
  conjunction `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` on this very topology.
- Every profinite target is `(S : Profinite.{u})`, including the empty one.
- X[S] is `(profiniteToProEtOf X).obj S`. Its inverse-limit interpretation and maps are
  supplied by `profinite_test_object_functor`, rather than by an arbitrary chosen scheme.
- The Hom set is `U ⟶ (profiniteToProEtOf X).obj S`, whose morphisms are exactly X-maps.
  The single existential family `e` consists of equivalences from these sets to
  `C(ConnectedComponents U.left, S)`, hence actual bijections of the required sets.
- Compatibility in S is the first equation: applying the functor to `b : S ⟶ T` and
  postcomposing f corresponds to postcomposition by b's underlying continuous map.
- Compatibility in U is the second equation, for every `a : V ⟶ U` between affine
  weakly contractible objects. It uses the canonical
  `a.left.continuous.connectedComponentsMap` with its existing continuity theorem.
  Thus both equations concern the same family of equivalences, rather than separately
  chosen bijections with no common naturality.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the recorded site dependency imports
  Mathlib's `Scheme.ProEt` and `Scheme.ProEt.topology`; its derived-category abbreviation
  is not needed here. This module is publicly imported through ProfiniteTestObjectFunctor.
- `Sheaf.Paper.ProfiniteTestObjectFunctor`:
  `AlgebraicGeometry.ProEtale.profinite_test_object_functor`, using the canonical
  `profiniteToProEtOf` from the exact side framework module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. Both signatures and docstrings
  were read, including the finite-quotient limit clause and the base-change construction.
- `def-weil-size-convention` is a metatheoretic convention, rendered by explicit universe u
  and the larger Type (u+1) sheaf values, as its record requests.
- Proof imports: `Mathlib.AlgebraicGeometry.Properties`, `Mathlib.Topology.Spectral.Basic`
  (the qcqs/spectral Mathlib leaves), and
  `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`
  (`AlgebraicGeometry.coproductCopiesMorphismsClopen`, full signature/docstring read).
  The component/clopen-intersection proof node has no recorded declaration or Mathlib
  match in this checkout, so no import can yet be included for it. It is only a proof
  dependency and is not needed to type the present statement.

Edge cases: empty U gives an empty component quotient and a unique function to every S;
empty S gives no functions for nonempty U and a unique function for empty U. These cases
are not excluded by the binders. A singleton S gives one morphism over X and one function.
No connectedness, nonemptiness, Hausdorffness of U, or compactness of X is assumed. The
quotient, rather than U, is asserted Hausdorff. The weak-contractibility hypothesis is
retained even though the finite-quotient proof works for all affine U.

Searches for an existing statement (2026-10-15):

- msearch leansearch: “Maps from an affine proetale scheme to a profinite test scheme
  are continuous maps from the connected component quotient”. Service unavailable:
  Internal Server Error; no absence inference from this search.
- msearch leanfinder: “Morphisms from an affine scheme over X to the profinite test scheme
  X[S] correspond naturally to continuous maps from connected components to S”. Eight
  hits concern affine-space Hom equivalences and affine inverse limits; none matches.
- msearch loogle: `ConnectedComponents, ContinuousMap`. Three hits, including
  `continuousMapPresheafEquivOfTotallyDisconnectedSpace` and geometrically-connected
  component homeomorphisms. These do not identify scheme maps into X[S].
- msearch grep: `ConnectedComponents|connectedComponents` in AlgebraicGeometry. Eight
  hits in Geometrically/Connected and Sites/ConstantSheaf, none the required statement.
- rg in upstream WeilConjectures for connected-components and contractibility names:
  spectral-space quotient lemmas and ring-theoretic w-contractibility, no full Hom statement.
  Searching the item id there gives no match.
- rg in lean/Sheaf: no existing component/test-object Hom correspondence. The affine
  hypercover theorem already uses precisely the inline sheaf-epimorphism condition used here.
- Read the Bhatt–Scholze PDF at Lemma 4.2.13: its proof explicitly states
  `(S tensor X)(U) = Map_cont(pi_0(U), S)`. Its qcqs-base topos assertions are not used
  to impose a hypothesis on X; the node's finite-coproduct/inverse-limit proof is retained.
  Read coord/pefw-upstream-framework.md and the exact framework Basic.lean.

No statement correction, new nodes, dependency repair, or disputed statement.
The theorem docstring carries all five proof steps and their DAG references.
Validation uses only server scompile.py and the prescribed delivery dry run.

## Second reading by NI

Independent second reading, 2026-10-15. I read the delivered node, the entire module,
all statement-dependency statements and recorded interfaces, the exact side-framework
Basic.lean construction, and the available proof interfaces. No mathematical mismatch
was found; the Lean module and node signature are retained verbatim.

Object, hypothesis and conclusion checklist:

1. Arbitrary base scheme X: `X : Scheme.{u}`. Mathlib's Scheme and Hom are schemes
   and locally ringed-space morphisms. Verdict: exact; no qcqs, Noetherian, separated,
   nonempty, characteristic or field hypothesis is added.
2. Small pro-etale object U: `U : X.ProEt`, with underlying scheme `U.left`.
   I read Mathlib Sites/Proetale: this is `MorphismProperty.Over @WeaklyEtale ⊤ X`,
   with all X-morphisms and the induced fpqc/weakly-etale topology. This is the site
   imported by the dependency ProEtaleDerivedCategory. Verdict: exact.
3. Affineness: `IsAffine U.left`. Verdict: exact; no affine presentation chosen.
4. Weak contractibility: the implication from
   `∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
   Epi f → Function.Surjective (f.hom.app (op U))`.
   This quantifies over all set-sheaf epimorphisms and evaluates at U, rather than
   assuming every presheaf map is pointwise surjective. Verdict: exact.
5. Every profinite S: `S : Profinite.{u}`. The dependency uses precisely the smaller
   universe's compact Hausdorff totally disconnected spaces. Verdict: exact.
6. X[S]: `(profiniteToProEtOf X).obj S`. I read the actual definition in the 51-module
   framework: base change of `Spec LC(S, ℤ)` along `toSpecZ X`. The recorded theorem
   profinite_test_object_functor identifies its finite values with coproducts of X
   naturally and sends every finite-quotient limiting cone to a limiting cone over X.
   Thus the construction is the node's inverse limit, with its canonical maps; no
   arbitrary comparison or replacement test object is introduced. Verdict: exact.
7. Component quotient: `ConnectedComponents U.left`. I checked Mathlib's connected
   component setoid and its quotient-topology instance, with `isQuotientMap_coe`.
   The first conjunct asserts `CompactSpace`, `T2Space` and
   `TotallyDisconnectedSpace` of that quotient. Verdict: precisely profiniteness of
   the specified quotient, without asserting Hausdorffness of U.
8. Hom bijection: the single family `e`, universally quantified over all affine
   weakly contractible U and all S, has type
   `(U ⟶ (profiniteToProEtOf X).obj S) ≃ C(ConnectedComponents U.left, S)`.
   Morphisms in the over-site are exactly X-morphisms; `≃` supplies both directions
   and inverse laws. Verdict: exact.
9. Compatibility in S: the first equation sends `f ≫ (profiniteToProEtOf X).map b`
   to `b.hom.hom.comp (e U hU wU S f)` for every continuous target map b.
   Verdict: covariant naturality, exact composition order.
10. Compatibility in U: the second equation sends `a ≫ f`, for every `a : V ⟶ U`
    between objects satisfying the same two hypotheses, to precomposition with
    `a.left.continuous.connectedComponentsMap`. I read that map and its continuity
    theorem in Mathlib. Verdict: contravariant naturality of the same family e.

Source check: I independently read RefactorInstruction Section 4, eq:finite-XI,
eq:XS, lem:XS and the proof of lem:point-eval in the archived master source.
They give precisely the finite-coproduct and finite-quotient Hom correspondence.
I also read Bhatt–Scholze Lemma 4.2.13 and its proof from the local PDF: the
surrounding topos lemma assumes X qcqs and all schemes in that proof qcqs. Those
extra assumptions are not needed for the separate finite-quotient argument just
read in the master source: U is affine, and the limiting universal property is in
schemes over arbitrary X. I checked the Stacks topology.tex statements
lemma-connected-component-intersection and lemma-spectral-pi0; their compactness,
compact-open basis and intersection hypotheses apply to affine U. Hence the node
and its proof do not silently apply the stronger surrounding topos lemma.

Edge cases: empty U has empty component quotient and exactly one map to every
X[S]; empty S has no maps from nonempty U and one from empty U. Singleton S gives
one X-map. If X is empty, all objects over it are empty, so the same equations
remain valid. Zero rings/empty affine schemes are admitted. There is no n or
characteristic parameter. The binders impose no nonemptiness or connectedness.
The site retains object universe u+1 and morphism universe u; sheaf values are
Type (u+1), and test profinite sets and scheme carriers are in u, exactly as the
size convention and test-object dependency specify. No universe equality or
unbound variable was introduced.

Independent searches using different wording: msearch leanfinder queried
“Continuous functions from pi zero of an affine scheme classify maps over a base
into constant profinite schemes” (eight hits, affine-space Hom equivalences and
affine-limit section lemmas, no match); msearch loogle queried
`ConnectedComponents, LocallyConstant` (zero hits); msearch grep queried
`LocallyConstant|profinite` in `AlgebraicGeometry/Sites` (zero hits). Direct rg on
Mathlib AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf for
component/Hom equivalences and profiniteToProEtOf found only geometric-component
results, the framework construction and its test-object theorem, not this
statement. Existing generic component maps are reused. No duplicate notion,
new definition node or dependency module is needed.

H5/H6/H8/H9: the module adds one named theorem, with its whole proof `sorry`,
and no definition, axiom, private notation or local instance. Its docstring names
the source and blueprint and supplies all five node proof steps. The recorded
signature is verbatim the theorem signature. The absent component-intersection
proof-node interface is only a stage-3 proof dependency, not a missing object in
this statement; all currently recorded proof modules are imported.

Changes: only this independent reading was appended to the worker report; no
statement, hypothesis, dependency, declaration or docstring needed repair.

Validation: server scompile.py compiled ProEtalePointComponentsMaps.lean cleanly
in 1.6 seconds, nice 19, two threads, 60-second per-file limit. The side-only
import closure also compiled successfully under the same per-file settings.
