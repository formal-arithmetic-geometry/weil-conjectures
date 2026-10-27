## Worker report

The module `Sheaf.CategoryTheory.ScalarCompositorReplacementPasting` states
`CategoryTheory.ScalarCompositorReplacement.pasting`, with one `sorry` and no proved
theorems. The natural-language proof in its docstring gives all eight DAG steps.
The node is unchanged except for its `lean` record. There are no new nodes, dependency
repairs, statement corrections or disputed statements.

`System` and `ModelMaps` are records bundling the objects introduced inline in this
node, not new categorical notions. `ModelMaps.Compatible` is the conjunction of its
seven displayed model squares. They belong to this node and are listed with all
other helpers in `lean.declarations`. All data is explicit: lambda, source and target
isomorphisms are composites of Mathlib whiskerings; identity and composite model
maps use the six identity isomorphisms and six specified composites. No choice,
existence axiom, or postponed construction supplies any data.

Hypothesis and conclusion correspondence (all helper names below are in
`CategoryTheory.ScalarCompositorReplacement`):

- The six categories are `C0A`, `C1A`, `C2A`, `C0B`, `C1B`, `C2B`, each with its own
  object universe and morphism universe and its own `Category` instance. The twelve
  universes are explicitly declared; `autoImplicit` is false.
- The three coefficient functors are the parameters `T0`, `T1`, `T2`.
- The two replacement functors are the parameters `EA`, `EB`; the common comparison
  `σ : EA ⋙ T1 ⟶ T0 ⋙ EB` is exactly the node's sigma.
- For each R, F, P and Q are the six fields `System.FA`, `FB`, `PA`, `PB`, `QA`, `QB`.
  A `⥤` is Mathlib's `Functor`, including preservation of identities and composition.
- The isomorphisms c and alpha are `System.cA`, `cB`, `αA`, `αB`. A morphism between
  functors is Mathlib's natural transformation, and `≅` is the natural isomorphism
  in the functor category. This supplies exactly the component naturality and
  invertibility specified inline by the node.
- The coefficient transformations are `System.βF`, `βP`, `βQ`, with the source and
  target functors shown explicitly in their field signatures. None has an `IsIso`
  assumption. Sigma is also just a natural transformation.
- The first assumed equation is `System.replacement_square`:
  `βF ≫ whiskerLeft T0 cB.hom = whiskerRight cA.hom T1 ≫ σ`.
- The second assumed equation is `System.compositor_square`:
  `whiskerRight αA.hom T2 ≫ βQ = whiskerLeft FA βP ≫ whiskerRight βF PB ≫
  whiskerLeft T0 αB.hom`.
- `System.lambdaA` and `lambdaB` define exactly alpha after P of the inverse of c:
  `isoWhiskerRight S.cA.symm S.PA ≪≫ S.αA` and the corresponding B expression.
- The first conjunct of `pasting` is the inverse replacement square:
  `whiskerRight S.cA.inv T1 ≫ S.βF = σ ≫ whiskerLeft T0 S.cB.inv`.
- The next conjunct is `S.coefficientLeft = S.coefficientRight`. The left helper
  is `whiskerRight S.lambdaA.hom T2 ≫ S.βQ`. The right helper is
  `whiskerLeft EA S.βP ≫ whiskerRight σ S.PB ≫ whiskerLeft T0 S.lambdaB.hom`.
  Thus it is precisely the required coefficient equation for lambda.
- A second system `S'` has the same six categories and the same parameters
  T0, T1, T2, EA, EB and sigma. It carries exactly the same kinds of data and the
  same two assumed squares, through its `System` type.
- The six model isomorphisms rho are `ModelMaps.fA`, `fB`, `pA`, `pB`, `qA`, `qB`.
  The first two conjuncts of `ModelMaps.Compatible` are `c'_R rho_F,R = c_R`.
  The next two are the alpha model square, at A and B respectively:
  `whiskerLeft S.FA r.pA.hom ≫ whiskerRight r.fA.hom S'.PA ≫ S'.αA.hom =
  S.αA.hom ≫ r.qA.hom`, and its B counterpart. These are written in exactly
  the order of the node after reversing the notation for composition.
  Its final three conjuncts are the F, P, Q coefficient model squares,
  with source/target index pairs (0,1), (1,2), (0,2), respectively.
- Under `r.Compatible`, the first two model conclusions are
  `whiskerLeft EA r.pA.hom ≫ S'.lambdaA.hom = S.lambdaA.hom ≫ r.qA.hom`
  and the corresponding B equation: exactly lambda' after rho_P E equals rho_Q
  after lambda, separately for both rings.
- `ModelMaps.sourceIso` is exactly `T2(rho_P,A EA)`;
  `ModelMaps.targetIso` is exactly `rho_Q,B T0`. They are specified isomorphisms,
  not arbitrary identifications. The next two conclusions identify separately
  the primed left and right coefficient expressions under these endpoint maps:
  `r.sourceIso.hom ≫ S'.coefficientLeft = S.coefficientLeft ≫ r.targetIso.hom`,
  and the analogous equation with `coefficientRight`. The following iff states
  explicitly that the coefficient equations are equivalent.
- Cancellation when only F changes is the final conjunct of `pasting`. It fixes
  S.PA, S.PB, S.QA, S.QB, takes arbitrary replacement F's, c's, alpha's and rho_F's
  satisfying exactly the c and alpha model squares with identity rho_P and rho_Q,
  and concludes equality of the two replacement lambda transformations with
  S.lambdaA.hom and S.lambdaB.hom. The coefficient maps play no role in this
  cancellation, as in Step 4 of the DAG proof.
- Identity coherence is explicit: `(ModelMaps.refl S).Compatible` and its source
  and target identifications equal the identity isomorphisms. Its lambda formula
  is also included by specializing the universally quantified model formula to
  this identity model change. There is no choice of comparisons.
- Composition coherence quantifies over a third system S'' and a second compatible
  model change r'. It asserts `(r.trans r').Compatible`, both composite lambda
  model equations, and equality of the specified source and target isomorphisms
  to `r.sourceIso ≪≫ r'.sourceIso` and `r.targetIso ≪≫ r'.targetIso`.
  The separate left/right endpoint conclusions for the composite also follow by
  applying the same universally quantified clause to `r.trans r'`.
- All equations are equations of natural transformations, rather than merely
  equalities of components. Their input naturality is part of these Mathlib
  types, including naturality of both lambda isomorphisms. No additive, exactness,
  tensor or nonemptiness structure occurs anywhere.

Dependencies read and used:

- `def-nagata-category` is a Mathlib leaf with `mathlib_match` naming
  `CategoryTheory.Category` in `Mathlib.CategoryTheory.Category.Basic`. Its full
  signature, docstring and the `CategoryStruct` fields were read. The module's
  public import `Mathlib.CategoryTheory.Whiskering` imports this declaration.
- The same import supplies `CategoryTheory.Functor.whiskerLeft`, `whiskerRight`,
  `isoWhiskerLeft`, `isoWhiskerRight`; their full signatures and docstrings were
  read. `CategoryTheory.Functor` and `CategoryTheory.NatTrans` were read in
  `Mathlib.CategoryTheory.Functor.Basic` and `Mathlib.CategoryTheory.NatTrans`.
  Natural isomorphisms and their compositions use Mathlib's functor category.
- The sole proof dependency is again `def-nagata-category`; it is already imported.
  The blueprint source was read in full, including its Charts coefficient
  compatibility paragraph. The statement is the reviewed categorical calculation
  extracted from that paragraph, and needs no statement correction.

Edge cases checked before writing:

- Six empty categories give the empty functors and vacuous natural transformation
  equations. No `Nonempty` or selected object is needed by any definition.
- Terminal categories and identity c/alpha/model maps reduce the statements to
  the input squares; the identity and composite endpoint identifications remain
  genuine specified maps. Different object and hom universes are all permitted.
- In the one-object category of the multiplicative monoid of integers, take all
  functors to be identity, c and alpha and model isomorphisms to be identity,
  and all beta maps and sigma to be zero. The input squares and conclusions
  hold although none of the beta maps is invertible. This checks the important
  noninvertible coefficient case without adding an invertibility assumption.
- A change of only F with P,Q fixed and identity model comparisons reduces the
  model formula to equality of lambda, as recorded explicitly in the last clause.
- Two successive nontrivial P and Q model comparisons compose in the same order
  as `Iso.trans`; reversing the source's right-to-left notation gives exactly the
  order used in `ModelMaps.trans` and all five composite conclusions.

Searches for an existing exact statement:

- `msearch.py`, LeanFinder: "Replacing a functor by a naturally isomorphic functor
  in a compositor preserves coefficient natural transformation squares and is
  coherent with independent model isomorphisms". Eight hits, including
  `CategoryTheory.CatCommSq.iso`, `CategoryTheory.NatIso.hcomp` and Dold--Kan
  compatibility isomorphisms. These are ingredients or specialized constructions;
  none states replacement plus all three independent model changes and endpoint
  coherence for possibly noninvertible coefficient maps.
- `msearch.py`, Loogle: "CategoryTheory.NatTrans.naturality, CategoryTheory.CatCommSq".
  No hits for this joint query.
- `msearch.py`, Mathlib grep: "replacement|compositor|whisker.*exchange" in
  `CategoryTheory`. Twenty-five reported hits, chiefly monoidal whisker exchange,
  plus localization replacement objects and the Join exchange lemma; no exact match.
- `msearch.py`, LeanSearch: "Coefficient natural transformation squares are compatible
  with conjugating a compositor by a natural isomorphism and with model isomorphisms".
  Eight hits, including `NatTrans.naturality_2_assoc`, `TwoSquare.natTrans`,
  `NatTrans.mapSquare` and pseudofunctor naturality. None provides the whole statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, the upstream-name index and Mathlib
  CategoryTheory, using "ScalarCompositorReplacement|scalarCompositorReplacement|
  replacement.*pasting|compositor.*replacement": no exact notion/name match.
  The preliminary broader project search found only an unrelated signed double
  evaluation comment. Searching the node id in `lean/WeilConjectures` returned none.

Validation: the first server compile elaborated all declarations and found only
an ambiguous `open Functor` warning. It was corrected to `open CategoryTheory.Functor`.
The final compile and delivery preflight results are recorded below after running them.

Final validation: `scompile.py` compiled both the sandbox and library module names
without errors or warnings. `deliver2.py --no-push` then reported
`OK (dry run): commit e548990f5d6 passes the preflight and compiles; nothing pushed`.
The delivered delta contains only this module, the item's `lean` record, and this report.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
