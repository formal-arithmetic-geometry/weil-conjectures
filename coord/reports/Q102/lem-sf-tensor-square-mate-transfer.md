## Worker report

The module `Sheaf.CategoryTheory.Adjunction.TensorSquareMateTransfer` states
`CategoryTheory.tensorSquare_mate_transfer` and the unbounded ringed-site
identification `SheafOfModules.tensorSquareProjectionMap_ringed`. Both theorems
have `sorry` proofs. Four helper definitions contain actual data: the existing
right-adjoint projection map through an uncurried interface, the two composite
paths, and their specified common transpose. These are components of the item's
own construction, not independent notions or new DAG nodes. The item changes
only in its `lean` field. No statement correction or dependency repair is needed.

The mathematical source was read at `literature/stacks-project/sites-cohomology.tex`,
`equation-projection-formula-map` (Tag 0B56, lines 13660–13680) and
`remark-base-change` (Tag 07A7, lines 4032–4063). The first constructs the
unrestricted projection by transposing tensor comparison followed by the counit;
the second constructs the unbounded exchange mate by the same counit method.
The abstract mixed-action identity is the agent calculation stated and proved
in steps 1–6 of this node, not a theorem claimed verbatim from Stacks.

Hypothesis and conclusion correspondence:

- The four categories are `{A : Type uA} [Category.{vA} A]` and the corresponding
  independently universe-polymorphic binders for `B`, `C`, `D`. Their tensor
  bifunctors are `TA`, `TB`, `TC`, `TD`, each a functor from a product category.
  This supplies no associator, tensor unit, symmetry, or monoidal assumptions.
- `Pr : C ⥤ A`, `Rr : A ⥤ C`, `Pp : D ⥤ B`, `Rp : B ⥤ D`,
  `ar : Pr ⊣ Rr` and `ap : Pp ⊣ Rp` give exactly the two proper adjunctions.
  Their units and counits are those of the specified adjunction objects.
- `Pi : D ⥤ C`, `Pk : B ⥤ A`, `J : C ⥤ D`, `K : A ⥤ B` give the remaining
  functors. `theta : Pi ⋙ Pr ≅ Pp ⋙ Pk` is the specified identification
  Pr Pi ≅ Pk Pp, in Lean's diagrammatic functor order.
- `muR : TC ⋙ Pr ⟶ (Pr.prod Pr) ⋙ TA` and
  `muP : TD ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB` are natural tensor comparisons;
  neither is an isomorphism hypothesis.
- `di : (J.prod (𝟭 D)) ⋙ TD ⟶ ((𝟭 C).prod Pi) ⋙ TC ⋙ J` has precisely
  components JH tensor N → J(H tensor Pi N).
  `dk : (K.prod (𝟭 B)) ⋙ TB ⟶ ((𝟭 A).prod Pk) ⋙ TA ⋙ K` has precisely
  components KM tensor V → K(M tensor Pk V). Their types give naturality in
  both variables and do not require tensor comparisons on two J or K inputs.
- `a : J ⋙ Pp ⟶ Pr ⋙ K` is the given natural transformation.
  `square : ∀ H N, ...` is exactly the stipulated compatibility: Pp(di), then
  a at H tensor Pi N, then K(muR), equals muP, then a tensor identity, then dk.
  On the first side `K.map (TA.map (Prod.mkHom (𝟙 _) (theta.hom.app N)))`
  makes the node's suppressed Pr Pi N ≅ Pk Pp N transport explicit.
- `g` is always the recorded `mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)`.
  Reading `mateEquiv` and `mateEquiv_counit` checks that its component is the
  unit of ap followed by Rp(a) and Rp(K(counit ar)), in the required direction.
- `tensorSquareProjectionMap` uses `Adjunction.rightAdjointProjectionMap`
  through `Functor.curry.map mu` and `Functor.curryObjProdComp`. Its transpose
  is mu followed by counit tensor identity, as required for pi_r and pi_p.
  It does not use the iso-only `derivedProjectionFormulaMate` interface for
  the abstract statement.
- For every M, N, `Rr.obj M`, `Pi.obj N`, `Pr.obj (Pi.obj N)` and
  `TA.obj (M, Pr.obj (Pi.obj N))` are the node's E, X, T and Z. The common
  transpose definition explicitly contains
  `muR.app (Rr.obj M, Pi.obj N) ≫ TA.map (Prod.mkHom (ar.counit.app M) (𝟙 _))`,
  the specified c.
- `tensorSquareMateFirst` is di followed by J(pi_r), then g at Z.
  `tensorSquareMateSecond` is g tensor identity, then pi_p, then Rp(dk).
  Its final `Rp.map (K.map (TA.map (Prod.mkHom (𝟙 M) (theta.inv.app N))))`
  transports to the chosen Z. This is precisely the stated second path under
  the supplied identification, rather than a strict equality of functors.
- The last two conjuncts in `tensorSquare_mate_transfer` assert separately that
  `(ap.homEquiv _ _).symm` of each path equals
  `tensorSquareMateCommonTranspose`, namely Pp(di), then a, then K(c).
- Its first two conjuncts identify both paths with `t.app (M,N)` for one
  natural transformation `t` from `((Rr ⋙ J).prod (𝟭 D)) ⋙ TD` to
  `((𝟭 A).prod (Pi ⋙ Pr)) ⋙ TA ⋙ K ⋙ Rp`. This states equality naturally in
  M and N, not just pointwise equality with no naturality assertion.
- There are no IsIso assumptions on a, its mate, the projections, muR, muP,
  di or dk, and no exactness, triangulated, boundedness or Tor hypotheses.
- `tensorSquareProjectionMap_ringed` takes arbitrary RingedTensorCorner data,
  a RingedTensorEdge, the two canonical tensor models, and arbitrary unbounded
  derived objects E and P. It identifies the projection above with the
  `derivedProjectionFormulaMate` appearing in the recorded
  `ringedProjectionMateExact` declaration. That declaration identifies its
  alpha component with this exact map; thus this is the node's final
  ringed-site scope and normalization clause.

Dependency declarations read and used:

- `def-nagata-category`: Mathlib.CategoryTheory.Category.Basic,
  `CategoryTheory.Category` (including CategoryStruct and the category laws).
- `def-weil-pbc-adjunction-mate`: Mathlib.CategoryTheory.Adjunction.Mates,
  `CategoryTheory.mateEquiv`, with its unit/counit construction and
  `mateEquiv_counit`. This is a Mathlib leaf with no project `lean` record.
- `lem-weil-pbc-ringed-projection-mate-exact`: Sheaf.Paper.ProjectionMateExact,
  `SheafOfModules.ringedProjectionMateExact`, whose full signature and
  docstring were read. Its canonical models/edge and its alpha normalization
  are used by the second theorem; this module is publicly imported.
- `lem-weil-pbc-adjunction-of-natural-bijection`: Mathlib.CategoryTheory.Adjunction.Basic,
  `CategoryTheory.Adjunction.mkOfHomEquiv`, and `homEquiv`/`homEquiv_counit`.
  The file is already publicly imported by Mathlib.CategoryTheory.Adjunction.Mates.
- The existing canonical projection is
  `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`,
  `CategoryTheory.Adjunction.rightAdjointProjectionMap`; its full construction
  and `homEquiv_symm_rightAdjointProjectionMap_app_app` were read.
  It is exposed by the public import chain of ProjectionMateExact through
  ProjectionFormulaArrows. There is no duplicate construction of a projection.

Edge cases checked before writing: identity functors and identity adjunctions
reduce pi to mu and the asserted identity to the supplied square. With all
comparisons identities both paths and both transposes are identities. Empty
categories leave only the possible functors/adjunctions and vacuous components;
no chosen object or nonemptiness is imposed. Categories with zero objects and
zero input objects need no special instances. Noninvertible mu, a, di and dk
remain allowed: the only inverse used is the stipulated theta identification.
All eight object/morphism universe variables are bound independently, so
unequal site object and morphism universes are not excluded. General M,N are
used without any boundedness or Tor restrictions.

Searches for an existing statement (2026-10-22):

- msearch LeanFinder, `mixed tensor action compatible square transfers to
  adjunction mates with equal counit transposes`: eight hits, including
  mateEquiv_square, mateEquiv, and monoidal counit identities. These do not
  have the mixed domains or specified common-transpose conclusion.
- msearch Loogle, `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.homEquiv`:
  zero hits for that combined query.
- msearch LeanSearch, `mixed tensor action compatible square transfers to
  counit defined projection formula adjunction mates`: eight hits, including
  mateEquiv and mateEquiv_apply; none states this mixed-action result.
- msearch Mathlib grep, `mate.*[Pp]rojection|[Pp]rojection.*mate|frobeniusMorphism_mate`
  in CategoryTheory: three occurrences in Monoidal/Closed/Functor.lean.
  They concern the Frobenius morphism, not the present mixed-action square.
- rg on lean/WeilConjectures and lean/Sheaf for
  `derivedProjectionFormulaMate|tensor.*[Ss]quare.*[Mm]ate|mixed.*[Aa]ction`,
  and for the exact item id in WeilConjectures: the latter has no match.
  Read ProjectionMateSquareCoherence.lean: its square uses tensor comparisons
  on two inputs of the same horizontal functor and an invertible square, so
  does not state this mixed-action theorem. Read upstream ProjectionMapMate
  and MateTransport: their transport results require invertible horizontal
  comparisons/identifications and have different domains. Reused the generic
  rightAdjointProjectionMap instead of restating it.

Validation: scompile.py Q102 lem-sf-tensor-square-mate-transfer compiled the
module both as sandbox and library module successfully, with no diagnostics.
No global build or direct live-repository write was performed.

## Second reading by Q102

This is a second pass by the dispatched worker; the dispatch explicitly
prohibits starting another agent, so no independent-worker review is claimed.
The maintainer's independent delivery review remains separate.

Reopened the complete node statement and the delivered module after compiling.
Checked each of the four categories, eight functors, two adjunctions, theta,
four tensor bifunctors, two natural tensor comparisons, both mixed comparisons,
a, and the compatibility square against the binders above. In particular, di
uses N in D and dk uses V in B; neither was accidentally replaced by a
monoidal comparison. Checked the two directions of theta: the square ends
with theta.hom, while the second path ends with theta.inv to return to Z.
Checked that the first path applies its mate at Z, whereas the second applies
its mate at M. Checked both homEquiv inverse formulas against the actual
common-transpose definition and the order Pp(di), a, K(c). Checked that the
existential t is a natural transformation on A × D, with both paths as its
components, so the naturality clause has not disappeared. Finally compared
the unrestricted ringed theorem with the alpha normalization in the recorded
ringedProjectionMateExact signature. No mismatch was found and no statement
or dependency changes were necessary. All definitions have explicit data,
and both postponed theorems carry the corresponding natural-language proof.
