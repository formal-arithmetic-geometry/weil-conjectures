## Worker report

The module Sheaf.AlgebraicGeometry.BoundedDoubleGraphHilbertLocus states
AlgebraicGeometry.exists_bounded_double_graph_hilbert_locus with one sorry.
Four fully constructed canonical-map helpers adapt the recorded graph and
projective-space pullback maps to isomorphisms in the over category. They
introduce neither another Hilbert functor nor another polynomial predicate.
No statement correction, dependency repair, new node or disputed statement is needed.
Two already-landed definition nodes are added to stmt_deps because their declarations
are used: def-sfb-relative-morphisms-presheaf and
 def-sfb-projective-fibre-hilbert-polynomial.

Hypothesis and conclusion correspondence:

| Node | Lean |
| --- | --- |
| Noetherian affine U | U : Scheme.u, IsAffine U, IsLocallyNoetherian U. Affineness supplies compactness. |
| X and Y proper, flat and finitely presented | x and y, both IsProper, both Flat, both LocallyOfFinitePresentation. Properness supplies quasi-compactness and quasi-separatedness, so these are exactly finite presentation. |
| E is X times_U Y | pullback x y, structure map pullback.fst x y followed by x. |
| Specified closed embedding into P^m_U | m : Nat, j with the stated codomain, IsClosedImmersion j, and hj asserting that j is over U. ULift (Fin (m+1)) has exactly m+1 coordinates. |
| R rational and integer-valued on integers | R : NumericalHilbertPolynomial, the existing subtype with precisely this integrality condition. |
| Every geometric isomorphism graph has coordinate polynomial R | hR quantifies over every field Omega in universe u with IsAlgClosed, every Spec Omega to U, and every over-isomorphism of the two fibres. IsCoordinatePolynomial is applied to the actual graph followed by the canonical base change of j. |
| Hilbert functor of closed flat finitely presented families | properHilbertPresheaf of E to U. Properness is automatic inside projective E, so its proper-family convention excludes no family in the node. |
| H represents the functor | H : Over U and eH : RepresentableBy H. The identity gives the universal ideal, and homEquiv_comp gives its pullback. |
| Coproduct of projective polynomial strata | HP, inclusions iota, IsColimit of their cofan. Each inclusion is open and each component is IsHProjective. |
| H_P represents constant-P families | First iff: HasProjectiveFibreHilbertPolynomial versus unique factorization through iota P. This existing predicate uses eventual fibre Euler characteristics, identified by its definition node with the coordinate Hilbert polynomial for these projective families and after extension to geometric fields. hR uses the coordinate predicate directly. |
| H_X and H_Y open and characterized on every test scheme | HX, HY, iX, iY with IsOpenImmersion. Two iff statements say invertibility of the respective restricted projection is equivalent to unique factorization through the corresponding open. The second-projection helper retains the test-coordinate of the recorded projection to Y. |
| J is their scheme-theoretic intersection | IsPullback pX pY iX iY, with pX composed with iX equal to iJ. This includes the restricted scheme structures and nilpotents. |
| J factors openly through H_R | r : J to HP R, r followed by iota R equals iJ, and IsOpenImmersion r.left. |
| J Noetherian and quasi-compact | IsNoetherian J.left and CompactSpace J.left. |
| J to U separated and finitely presented | IsSeparated, LocallyOfFinitePresentation, QuasiCompact and QuasiSeparated of J.hom, exactly the expanded convention in the node. |
| Points exactly closed families with both projections invertible | Iff for every Hilbert element D: the two IsIso predicates versus a unique a : T to J classifying D. Any closed subscheme with invertible first projection automatically has the Hilbert family properties, so this excludes no double graph. |
| Actual graph, every isomorphism, inverse bijections | eJ T is an equivalence of points with over-isomorphisms. The classified ideal equals the kernel ideal of doubleGraphMap, which is asserted a closed immersion. Surjectivity covers every isomorphism and injectivity gives uniqueness. |
| Projection identities and recovery p_Y composed with inverse p_X | Isomorphisms p and q have forward maps equal to the restricted projections, and p.inv followed by q.hom equals (eJ T a).hom.left. The graph ideal equality identifies the actual universal graph. |
| Naturality for every test morphism | The equation with Over.pullback x/y map h is naturality of eJ. Its inverse is natural by bijectivity. The next equation gives equality of pulled-back universal graph ideals by comap along baseChangeMap. Identities and composites are included. |
| Arbitrary new base U' | Final clause quantifies over every U' and g, without Noetherian or reducedness binders. eb represents the restricted Hilbert functor on the pullback of H; its values equal eH under the canonical map/pullback adjunction. |
| Pullback of H_R and J, universal graph and bijections | The constant-P iff identifies the pullback of every HP P, in particular R. ebJ gives isomorphism points on the actual pullback of J, with values pinned to eJ through the same canonical adjunction. Restricted functors evaluate at T to U' to U, the iterated-fibre-product realization of the pulled-back families. Thus the preceding actual-ideal and projection clauses apply to these same test schemes; no arbitrary replacement bijections are used. |
| No fibre-dimension bound | No dimension predicate occurs in the signature. |

Dependencies read in full and used:

- Mathlib.AlgebraicGeometry.Scheme: Scheme and scheme morphisms.
- Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian and IsNoetherian.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper, including separatedness.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: Flat.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: LocallyOfFinitePresentation.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, fst, snd, lift, with scheme pullbacks.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: IsHProjective and the canonical projective-space model.
- Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality: ProjectiveHilbertPolynomial.IsCoordinatePolynomial; its coordinate-piece and base-change definitions were also read.
- Sheaf.AlgebraicGeometry.ProperHilbertPresheaf: properHilbertPresheaf and IsProperHilbertFamily.
- Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion.
- Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf: relativeMorphismsPresheaf, relativeMorphismGraph, graphFirstProjection, graphSecondProjection. Its owning definition node is added to stmt_deps.
- Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial: NumericalHilbertPolynomial and HasProjectiveFibreHilbertPolynomial. Its owning definition node is added to stmt_deps.

Proof-only imports include ProjectiveHilbertPolynomialRepresentability and
GraphsOpenInHilbert, whose theorem signatures and docstrings were read. Mathlib
permanence inputs are available through the statement imports; the algebra
finite-presentation module is additionally imported for the Noetherian finite-type
argument. The theorem docstring carries all eight DAG proof steps, naming their
geometric and algebraic inputs.

Source check: read Stacks moduli-curves.tex lemma-curves-diagonal-separated-fp,
including the final fixed-polynomial bounded-open argument; quot.tex
lemma-Mor-into-Hilb and lemma-Mor-into-Hilb-open, including both proofs. The fixed
polynomial here is supplied as a hypothesis: no curve Riemann-Roch calculation or
curve-dimension assumption has been inserted.

Edge cases checked before drafting: empty U and empty test schemes; both families
empty (zero-polynomial graphs); one family empty and the other nonempty (no
isomorphisms); unrealizable R (empty graph locus); m=0; disconnected U with the
assumed common R for every geometric isomorphism; nonreduced T and T'; arbitrary
non-Noetherian U'; higher-dimensional fibres satisfying hR. None needs an extra
hypothesis. All schemes and fields have the same universe u; this includes
algebraic closures of their residue fields. All variables and universes are
explicit and both auto-implicit options are disabled.

Searches using the prescribed msearch.py wrapper:

- LeanFinder: Hilbert scheme open locus both projections isomorphisms fixed Hilbert polynomial separated finite presentation. Eight hits, including Proj pullback/properness and ordinary immersions; no matching statement.
- Loogle: AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.IsProper. Zero hits.
- Mathlib grep: Hilbert|hilbert|doubleGraph in AlgebraicGeometry. Zero hits.
- LeanSearch: Hilbert scheme of graphs of isomorphisms open locus fixed Hilbert polynomial. Eight hits on ordinary open immersions, isomorphisms, and restrictions; no Hilbert graph statement.
- rg of bounded Hilbert/double graph patterns on WeilConjectures and Sheaf: parent ProjectiveCurveIsomGraphs proof and unrelated Hilbert-weight modules, no fixed-polynomial double-graph theorem. Existing Hilbert, fibre-polynomial and relative-morphism definitions are reused.
- rg for each of the five proposed declaration names on Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no existing declaration.
- grep of the exact item id in WeilConjectures: no match.

Validation: scompile.py compiled both the sandbox module and its final library
module successfully, with no errors or warnings (7.5 s and 5.5 s). The prescribed
dry run and delivery follow. No global build, live-source edit or direct Git
command was used. The maintainer performs the independent review, as specified
by this dispatch; no independent worker reading is claimed here.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
