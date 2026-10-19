## Worker report

The module `Sheaf.Paper.AlterationFiniteRefinement` states
`AlgebraicGeometry.Orgogozo.exists_finite_surjective_refinement`. Its sole theorem has
`by sorry` as its entire proof. No definition, helper, dependency module, new node, or
statement correction is needed. Only the item's `lean` field changes.

### Statement correspondence

- “a : T → S” is `{T S : Scheme.{u}}` and `(a : T ⟶ S)`.
- “reduced Noetherian schemes” is `[IsReduced T] [IsReduced S] [IsNoetherian T]
  [IsNoetherian S]`. Mathlib's `IsNoetherian` extends both `IsLocallyNoetherian` and
  `CompactSpace`; it is the global notion required by the node and the dependency.
- “a is an alteration” is `(ha : IsAlteration a)`, the recorded dependency predicate:
  proper, surjective, finite over a dense target open, with the closure of the image of
  each source component a target component.
- “there exist modifications u : T̃ → T and v : S′ → S” is
  `∃ (T' S' : Scheme.{u}) (u : T' ⟶ T) (v : S' ⟶ S) ...,
  IsModification u ∧ IsModification v ∧ ...`. The recorded predicate includes properness,
  an isomorphism over a dense target open, and density of that open's inverse image.
- “finite surjective p : T̃ → S′” is `(p : T' ⟶ S')` with `IsFinite p ∧ Surjective p`.
- “a u = v p” is `u ≫ a = p ≫ v`, with Lean's diagrammatic composition order.
- “if S is integral, S′ and T̃ may be taken reduced” is
  `IsIntegral S → IsReduced S' ∧ IsReduced T' ∧ ...` inside the same existential.
- “with S′ integral when T is integral” is the final `(IsIntegral T → IsIntegral S')`
  under the `IsIntegral S` implication. Neither input is assumed integral globally.

There is one explicit universe `u`, consistently used for all schemes. There are no
auto-bound variables, hidden structure choices, extra hypotheses on witnesses, or
file-local notation. The existential witnesses simultaneously satisfy every requested clause.

### Dependencies and source reading

Read both statement-dependency nodes in full and their recorded declarations:

- `def-trf-orgogozo-induction-data`: public import
  `Sheaf.Paper.OrgogozoInductionData`; use
  `AlgebraicGeometry.Orgogozo.IsAlteration` and
  `AlgebraicGeometry.Orgogozo.IsModification`. Read the complete module, including both
  signatures and source docstrings. The modification predicate's reduced/Noetherian
  target instances are supplied by the input binders, without any interface repair.
- `def-weil-finite-integral-morphism`: public import
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`; use `AlgebraicGeometry.IsFinite`.
  Read the full `IsFinite` and `IsIntegralHom` signatures and docstrings in Mathlib.
  `IsFinite` is the affine-local finite ring-map definition in the node. The integral
  morphism predicate is not needed here; integral schemes use `IsIntegral` instead.

Read Mathlib's definitions of `IsReduced`, `IsIntegral`, and `IsNoetherian`.
Read the online author PDF at the source URL in the node, §1 and Lemma 2.5 on printed
p. 4 (PDF page index 3). Lemma 2.5 states the finite-surjective commuting square with
both horizontal arrows modifications. Its reduced-base proof uses generic flatness
and flattening; the node spells out the strict-transform and component arguments and
adds the reducedness/integrality consequences of that construction. The complete ten
proof steps of the node appear in the theorem docstring, including the empty-base case.
Source: [Orgogozo, author PDF](https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Modifications%20et%20cycles%20proches%20sur%20une%20base%20g%C3%A9n%C3%A9rale.pdf).

All recorded proof modules are imported without `public`. For the component-coproduct
and reduced-induced-closed-subscheme modules absent from the local upstream checkout,
`scompile.py --source WeilConjectures.AlgebraicGeometry.DenseOpenComponentCoproduct` and
`scompile.py --source WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
confirmed their current published sources. These upstream modules are used instead of
importing the duplicate local `Sheaf` modules. `lem-trf-finite-after-blowup` currently has
neither a Lean record nor a Mathlib match, so no module for that proof-only dependency
can yet be imported; it is not needed to state the theorem.

One inherited proof-record fault is outside this delivery's statement interface:
`lem-pc-closed-imm-base-change` records `AlgebraicGeometry.IsVeryAmple.pullback_of_field`
in `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`, which concerns very ampleness,
not stability of closed immersions under base change. The recorded module is imported
as required, but the proof should use Mathlib's closed-immersion base-change instance.
This fault does not affect any notion in the statement or require changing the item.

### Edge cases checked

- Empty S forces empty T; the empty schemes and identity modifications give the
  refinement. The statement has no `Nonempty` assumptions, and the integral-base
  implication is vacuous in this case.
- Identity alterations and finite surjective alterations admit identity modifications.
- Reducible S and reducible T are retained. No irreducibility or integrality hypothesis
  is imposed by the theorem or its modification predicate.
- Integral S with reducible T: the reducedness clause applies, while the integrality
  of T remains a conditional premise for the final conclusion, exactly as written.
- Integral T and integral S: the same witnesses give reduced T′ and integral S′.
- Density of the inverse isomorphism locus is retained on both modifications, preventing
  added vertical components from satisfying a weaker modification predicate.

### Searches for an existing statement

The searches were made with the prescribed `msearch.py Q17
lem-trf-alteration-finite-refinement` wrapper; its raw records are in the sandbox's
`searches.jsonl`.

- LeanFinder query: “An alteration of reduced Noetherian schemes admits modifications
  of source and target making it finite surjective”. Eight hits were ordinary finite,
  finite-type, integral, and quasi-finite morphism interfaces; none states this theorem.
- Loogle query: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProper`. Nine hits give
  finite implies proper, the proper/affine characterization, proper quasi-finite implies
  finite, and local finite-locus assertions; none provides the alteration square.
- Mathlib grep query: `alteration|IsAlteration|IsModification|finite.*strictTransform`
  in `AlgebraicGeometry`: zero hits.
- LeanSearch query: “alteration admits finite surjective refinement over modification
  of Noetherian scheme”. Eight hits describe finite and surjective scheme morphisms and
  stability under base change; none is the desired refinement.
- `rg` of the upstream `WeilConjectures` sources for alteration/modification and for the
  exact node id found no existing statement. Searching the upstream-name index found
  no matching alteration/refinement declaration.
- `rg` of the shared `lean/Sheaf` sources finds the recorded geometric predicates and
  the future use of this lemma in `OrgogozoGoodModification`, but no statement of the
  lemma. Searching the proposed declaration name finds the different theorem
  `Scheme.exists_finite_surjective_refinement_of_etale`; that theorem refines an étale
  cover and does not assert the two modifications of an alteration.

No STATEMENT-DISPUTED flag: the statement is retained verbatim.

### Validation

The delivered module is checked through `scompile.py` alone. The delivery dry run and
final push run the server preflight and per-file compilation again. No global build or
direct Git command is run in either read-only checkout.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
