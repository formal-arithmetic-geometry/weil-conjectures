# Finite type along an fppf source-algebra map

## Worker report

Module `Sheaf.RingTheory.FiniteTypeFppfSourceDescent` states
`RingHom.finiteType_of_comp_faithfullyFlat_finitePresentation`, with proof `sorry`.
It introduces no definition and proves nothing. Its source is Stacks Project,
Descent, Tag 0367, `lemma-finite-type-local-source-fppf-algebra`, read in
`literature/stacks-project/descent.tex`, lines 4351–4386. The source says exactly:
ring maps R → A → B, finite type of the composite, faithful flatness and finite
presentation of the second map, finite type of the first map.

Hypothesis and clause correspondence:

| Node clause | Lean |
| --- | --- |
| R, A, B are commutative rings | `{R : Type uR} {A : Type uA} {B : Type uB}` and `[CommRing R] [CommRing A] [CommRing B]` |
| Ring homomorphisms R → A → B | `(f : R →+* A) (g : A →+* B)` |
| R → B is their composite | `g.comp f`; no independently chosen third map or compatibility premise |
| B is of finite type over R through that composite | `(hB : (g.comp f).FiniteType)` |
| A → B is faithfully flat | `(hflat : g.FaithfullyFlat)` |
| A → B is of finite presentation | `(hfp : g.FinitePresentation)` |
| A is of finite type over R | conclusion `f.FiniteType` |
| No Noetherian hypothesis on any ring | no `IsNoetherianRing` or Noetherian assumption is present |

The three universes `uR`, `uA`, `uB` and all variables are explicitly bound;
`set_option autoImplicit false` enforces this in the module. No hypothesis is
added about injectivity, nontriviality, characteristic, size, or a scalar tower.
All algebra structures are the canonical ones induced by the indicated maps.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Mathlib.RingTheory.FiniteType`. Its definition is
  `@Algebra.FiniteType R A _ _ f.toAlgebra`, so it is exactly finite generation
  for the given map, not an independently selected algebra structure.
- `def-weil-pbc-faithfully-flat-ring-map`: `RingHom.FaithfullyFlat`,
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`, recorded in the dependency's
  `lean.declarations` and `mathlib_match`. It installs `g.toAlgebra` and uses
  `Module.FaithfullyFlat A B`, whose recorded module
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` is publicly imported as well.
  The equivalence with preservation and reflection of exactness is
  `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`; its full signature was read.
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`,
  `Mathlib.RingTheory.FinitePresentation`, through its ring-map form
  `RingHom.FinitePresentation` (also explicitly named by the node's
  `mathlib_match`). The latter is definitionally
  `@Algebra.FinitePresentation A B _ _ g.toAlgebra`. The former states a
  surjection from a finite-variable polynomial ring with finitely generated
  kernel. Thus no dependency repair or private definition is needed.

The six proof steps of the node are reproduced in the declaration docstring:
integer fppf model; base extension T; finite coefficient polynomial enlargement P;
faithfully flat Q = P ⊗[C] D and its surjection to B; tensor comparison and
exactness reflection; finite generation of the quotient A. The proof-only imports
provide `Algebra.TensorProduct.productMap` and the tensor construction of
`lem-weil-pbc-algebra-tensor-pushout-universal-property` and
`def-weil-pbc-module-tensor-product`. Faithfully flat base change is already
available from the imported faithfully flat module. The proof prerequisite
`lem-a1-fppf-integer-model` has no recorded Lean module in the read-only DAG,
so there is no module to import for it; it is cited in the proof docstring.
It supplies no notion needed by the statement and is not restated here.

Edge cases checked before writing:

- Zero rings are permitted. If B is the zero ring, faithful flatness forces A
  to be the zero ring; the conclusion remains true. R can be zero only when
  the target rings of its unital maps are zero. No `Nontrivial` excludes these.
- Identity maps are permitted. If g is the identity, the conclusion is the
  given finite-type premise. If f is the identity, its conclusion is automatic.
- Zero algebra generators and empty lists of relations are allowed by Mathlib's
  finite-type and finite-presentation definitions (including polynomial rings
  in zero variables). Nothing in this signature excludes them.
- Rings of all characteristics and non-Noetherian rings are included. No
  conversion from finite type to finite presentation is assumed for R → B.
- Independent ring universes are retained; there is no quantification over
  small test rings that could make a hypothesis vacuous.

Searches (all made with the prescribed wrapper or read-only rg/grep):

- LeanFinder: `A ring map R to A is finite type if R to B is finite type and
  A to B is faithfully flat and finitely presented`. Eight hits: stability
  under base change, essential finite type, scalar restriction of finite
  presentation, and `RingHom.FinitePresentation.of_comp_finiteType` among them.
  None concludes finite type of the first map under the node's hypotheses.
- Loogle: `RingHom.FiniteType, RingHom.FaithfullyFlat`. One hit:
  `RingHom.FiniteType.codescendsAlong_faithfullyFlat`. Read the complete theorem
  and `RingHom.CodescendsAlong` in `Mathlib.RingTheory.RingHomProperties`:
  it descends a property along a base-change pushout square, rather than the
  source-algebra tower of this node. It is not the same statement.
- LeanSearch: `Finite type in a ring tower R to A to B descends when A to B
  is faithfully flat of finite presentation`. Eight hits on flat descent,
  finite-presentation definitions and composition/scalar restriction; none
  is the stated tower finite-type descent theorem.
- Mathlib grep through msearch:
  `finiteType.*(faithfully|descent)|finite_type.*faithfully|FaithfullyFlat.*FiniteType`
  in `RingTheory`. Six hits, all tensor-product base descent or its use.
  Read `Mathlib.RingTheory.Finiteness.Descent` in full; none states this lemma.
- The same conceptual pattern searched by rg in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf`:
  no matching theorem. `grep -rn` for the item id in the source library:
  no result.
- Additional rg for
  `finiteType.*[Ff]ppf|finiteType.*[Ss]ource|finite_type.*[Ff]ppf|finite_type.*[Ss]ource`
  in source/library/upstream-name index: one unrelated coherent-module use,
  no statement matching this item. The proposed full declaration name was
  also searched in Mathlib, source, side library, and upstream-name index:
  no collision.

No statement correction, new node, dependency repair, or disputed statement.
The retained previous attempt's interpretation of Q11's review was checked:
Q11 delivered the stage-1 split, and the actual node has no `lean` field.
The delivery now supplies the missing stage-2 record and module.

## Second reading by Q05

Self-check by the dispatcher worker, with both the node JSON and final module
open; no separate agent was started, as the task explicitly forbids doing so.
The maintainer supplies the independent review.

Re-read the source lemma, dependency definitions, and each binder. The three
commutative-ring types correspond exactly to R, A, B, with independent universes.
The two homomorphisms and their explicit composite match the node's tower.
`hB` is finite type of R → B, not of A → B. `hflat` and `hfp` both concern g,
and the conclusion concerns f. The ring-map predicates use the algebra structure
of these maps, so no unnamed structure or compatibility premise has been added.
There is no Noetherian or nonzero-ring restriction. The definition of faithful
flatness agrees with the recorded exactness characterization. Finite presentation
uses exactly the recorded polynomial-quotient definition via its ring-map wrapper.
The proof is only `sorry`, and the docstring retains all six node proof steps.
No mismatch in the statement was found and no mathematical change was made.

## Validation

`scompile.py Q05 lem-a1-finite-type-fppf-source-algebra <module path>` passed:
sandbox check 9.7 s, library-path check 33.8 s, no errors or warnings.
The node differs from the read-only base only in `lean`; its recorded signature
matches the module verbatim, all source lines are at most 89 characters, and
the only theorem proof is `sorry`.
`deliver2.py Q05 lem-a1-finite-type-fppf-source-algebra --no-push` passed:
`OK (dry run): commit ed1f07dabf passes the preflight and compiles; nothing pushed`.
