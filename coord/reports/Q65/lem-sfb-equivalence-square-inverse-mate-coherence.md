## Worker report

Item: `lem-sfb-equivalence-square-inverse-mate-coherence`.
Module: `Sheaf.CategoryTheory.EquivalenceAdjunctionComparison`.

This delivery states the node's three clauses as three theorems. Each has exactly
one postponed proof (`by sorry`); it introduces no definitions and proves nothing.
The node's statement, statement dependencies and proof plan are unchanged. Its
`lean` record lists all three declarations and records the first signature verbatim.

Read the node and every statement dependency, including the full signatures and
docstrings of `mateEquiv`, `Adjunction.comp` and `conjugateEquiv`. Also read the
proof dependencies' recorded declarations. Read Stacks `categories.tex`,
`lemma-transformation-between-functors-and-adjoints` (Tag 0B65), and the current
blueprint's `det-nagata-density-normalization-sheaves.proof.md`, Steps 1–2. The
node explicitly supplies the agent-written categorical extension beyond the
Stacks lemma; its eight detailed proof steps are retained in the three docstrings.
There is no repair note for this item.

### Hypotheses and clauses

All categories use separate, explicitly declared object and morphism universes:
`A`, `B`, `C`, `D`, `Ab`, `Bb`, `Cb`, `Db` have their own `Type` and `Category`
binders. Functional composition VU in the node becomes `U ⋙ V` in Lean.
The barred suffix `b` denotes the corresponding barred category or functor.

| Node text | Lean rendering |
| --- | --- |
| (1) Specified equivalences between A, B and their barred categories | `EA : A ≌ Ab`, `EB : B ≌ Bb` |
| Specified J left adjoint to U and barred J left adjoint to barred U | Functors `J`, `U`, `Jb`, `Ub`, and `adj : J ⊣ U`, `adjb : Jb ⊣ Ub` |
| Specified natural isomorphism u : E_A U ≅ barred U E_B | `u : U ⋙ EA.functor ≅ EB.functor ⋙ Ub` |
| There is a natural isomorphism j : E_B J ≅ barred J E_A | `∃ j : J ⋙ EB.functor ≅ EA.functor ⋙ Jb` in `exists_equivalenceAdjunctionComparison` |
| Its inverse has mate u | `(mateEquiv adj adjb j.inv).natTrans = u.hom` |
| Uniqueness under exactly this normalization | Every `k` of the same isomorphism type whose inverse has mate `u.hom` satisfies `k = j`; uniqueness does not require the other conclusions as extra hypotheses |
| Identification of the full Hom bijections | For every `X`, `Y`, and `f : J.obj X ⟶ Y`, the barred transpose of `j.inv.app X ≫ EB.functor.map f` equals `EA.functor.map (adj.homEquiv X Y f) ≫ u.hom.app Y` |
| Unit identification | `adjb.unit.app (EA.functor.obj X) ≫ Ub.map (j.inv.app X) = EA.functor.map (adj.unit.app X) ≫ u.hom.app (J.obj X)` for every X |
| Counit identification | `j.inv.app (U.obj Y) ≫ EB.functor.map (adj.counit.app Y) = Jb.map (u.hom.app Y) ≫ adjb.counit.app (EB.functor.obj Y)` for every Y |
| Analogous assertion for the primed adjunctions on C, D and their barred categories | Instantiate the same universally quantified theorem with `(A,B,Ab,Bb,EA,EB,J,U,Jb,Ub,adj,adjb,u)` replaced by `(C,D,Cb,Db,EC,ED,J',U',Jb',Ub',adj',adjb',u')`; no primed case or conclusion is omitted |
| (2) Three categories on each side and equivalences E_i | `equivalenceAdjunctionComparison_compositor` uses A, B, C and Ab, Bb, Cb, with `E0`, `E1`, `E2` |
| Specified three adjunctions and their barred counterparts | `adj01`, `adj12`, `adj02`, `adjb01`, `adjb12`, `adjb02`, with all six pairs of functors explicitly bound |
| Right comparisons r_ij | `r01`, `r12`, `r02` with types `Rji ⋙ Ei.functor ≅ Ej.functor ⋙ Rbji` |
| Normalized left comparisons c_ij from (1) | `c01`, `c12`, `c02`, and precisely the three mate-normalization hypotheses `h01`, `h12`, `h02` |
| Specified delta and barred delta | `delta : R21 ⋙ R10 ≅ R20`, `deltab : Rb21 ⋙ Rb10 ≅ Rb20` |
| Their right-comparison compatibility | `hdelta` states the displayed three-factor right route equals `E0.functor.map (delta.hom.app Z) ≫ r02.hom.app Z` for every `Z : C` |
| Adjoint compositors a, barred a | `a : L01 ⋙ L12 ≅ L02`, `ab : Lb01 ⋙ Lb12 ≅ Lb02` |
| Conjugates of a, barred a are delta inverse, barred delta inverse | `ha : conjugateEquiv adj02 (adj01.comp adj12) a.hom = delta.inv` and the corresponding `hab` using the barred adjunctions |
| The left-compositor compatibility conclusion | For every X, `E2.functor.map (a.hom.app X) ≫ c02.hom.app X = c12.hom.app (L01.obj X) ≫ Lb12.map (c01.hom.app X) ≫ ab.hom.app (E0.functor.obj X)` |
| (3) All four categories, equivalences, two pairs of adjunctions, and normalized comparisons from (1) | `equivalenceAdjunctionComparison_inverseMate` binds `EA`, `EB`, `EC`, `ED`; `adj`, `adj'`, `adjb`, `adjb'`; `u`, `u'`, `j`, `j'`; and their normalizations `hj`, `hj'` |
| Functors P, Q, barred P, barred Q | `P : A ⥤ C`, `Q : B ⥤ D`, `Pb : Ab ⥤ Cb`, `Qb : Bb ⥤ Db` |
| Isomorphisms p and q | `p : P ⋙ EC.functor ≅ EA.functor ⋙ Pb`, `q : Q ⋙ ED.functor ≅ EB.functor ⋙ Qb` |
| Right squares b and barred b | `b : U ⋙ P ⟶ Q ⋙ U'`, `bb : Ub ⋙ Pb ⟶ Qb ⋙ Ub'`; these are arbitrary natural transformations |
| Compatibility of those squares | `hb` is exactly the node's equation evaluated at every `Y : B`, with `p`, `u`, `bb` on the left route and `EC.map b`, `u'`, `Ub'.map q` on the right |
| Beta and barred beta are the actual inverse mates | Written directly as `((mateEquiv adj adj').symm b)` and `((mateEquiv adjb adjb').symm bb)`; no arbitrary comparison map or extra mate hypothesis replaces either construction |
| Equality of the actual inverse-mate comparison transformations | First conclusion conjunct: the node's equation at every X, in Lean's left-to-right composition order |
| Beta invertible iff barred beta invertible | Second conjunct: `IsIso (((mateEquiv adj adj').symm b).natTrans) ↔ IsIso (((mateEquiv adjb adjb').symm bb).natTrans)` |
| Canonical associators, with no strict identity assumptions | All diagram equalities are universal component equalities. Their equivalence to the transformations' equality is `NatTrans.ext`; canonical functor associators have identity components. No functor equality, identity unit/counit, or identity comparison is assumed |

The three equivalences and six adjunctions in clause (2), and the eight categories in
clause (3), retain independent size parameters; no universe equality is imposed.
The first theorem can be instantiated independently twice, so the node's unprimed
and primed assertions hold together with exactly their respective data.

### Dependency declarations used

- `def-weil-pbc-adjunction-mate`: `CategoryTheory.mateEquiv` and its inverse,
  `Mathlib.CategoryTheory.Adjunction.Mates`, as recorded in `mathlib_match`.
- `def-weil-pbc-composite-adjunction`: `CategoryTheory.Adjunction.comp`,
  `Mathlib.CategoryTheory.Adjunction.Basic`, re-exported by Mates.
- `def-weil-pbc-adjunction-conjugate`: `CategoryTheory.conjugateEquiv`,
  `Mathlib.CategoryTheory.Adjunction.Mates`.
- Proof dependency `lem-pur-adjunction-mate-transpose`:
  `CategoryTheory.adjunctionMate_transpose`, imported non-publicly from
  `Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose`.
- Proof dependency `lem-stage3-inverse-mate-equivalences`:
  `CategoryTheory.isIso_inverseMate_of_equivalences`, imported non-publicly from
  `WeilConjectures.CategoryTheory.InverseMateEquivalence`.
- Proof dependency `lem-weil-pbc-mate-pasting`: recorded Mathlib declarations
  `mateEquiv_hcomp`, `mateEquiv_vcomp`, `mateEquiv_conjugateEquiv_vcomp`,
  `conjugateEquiv_mateEquiv_vcomp`, `conjugateEquiv_id`, all in the already
  publicly imported Mates module. No proof dependency import is omitted.

### Searches

Used the prescribed `msearch.py Q65 <item>` wrapper:

- LeanFinder: `Equivalences of categories preserve normalized adjunction comparisons,
  adjoint compositors and inverse mates of natural transformations`; repeated with
  `Equivalences transport adjunctions with unique normalized left comparisons
  preserving inverse mates`. Hits include `mateEquiv`, `mateEquiv_apply`,
  `mateEquiv_symm_apply`, `mateEquiv_counit_symm`, bicategorical mate definitions,
  `Equivalence.trans_toAdjunction`, `iterated_mateEquiv_conjugateEquiv`. None states
  the three clauses of this node.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.conjugateEquiv` gives
  `conjugateEquiv_mateEquiv_vcomp`, `mateEquiv_conjugateEquiv_vcomp`, and the two
  iterated conjugate-equivalence identities. These are pasting tools, not this
  normalized-equivalence comparison statement.
- Mathlib grep: `mateEquiv_square|mateEquiv_hcomp|unit_mateEquiv_symm`, restricted
  to `CategoryTheory/Adjunction`, gives four hits in Mates. Read the source:
  `mateEquiv_square` pastes four arbitrary squares and does not assert normalized
  comparison existence, compositor transport or the actual inverse-mate square
  under the given compatibility hypothesis.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for equivalence/mate and
  normalized-comparison patterns, and the prescribed node-id grep upstream:
  no exact node statement. Examined `AdjunctionComparisonSquare.lean`:
  `Adjunction.rightAdjointUniq_square` concerns two adjunctions between the same
  pair of categories and compatible counit squares; it does not provide this node.
  The upstream inverse-mate equivalence theorem proves an ingredient of (1).
- Exact proposed declaration names searched in Mathlib, upstream, Sheaf, and
  `dag/lean_names_upstream.json`: no collision.

### Edge cases checked before writing

Empty categories require no new inhabitedness or chosen objects. Identity
adjunctions and equivalences are admitted, but no identity assumption is used.
Nontrivial adjunction units/counits and natural automorphisms remain specified.
The normalization uses the inverse of j, not its forward map; conjugation reverses
direction, hence the compositor hypotheses correctly use delta inverse. Direct
and composite adjunctions may be different specified adjunctions on their functors.
The transformations b and bb may be noninvertible, and P, Q, Pb, Qb need no adjoints.
The final invertibility assertion is about the inverse mates themselves, not b or bb.
All category and morphism universes remain independent. No edge case requires a
statement correction, and there is no STATEMENT-DISPUTED flag.

### Validation

The prescribed compile wrapper initially encountered missing published Mathlib
artifacts (`Adjunction.Mates.olean`, then `Adjunction.FullyFaithful.olean`). These
transient environment failures resolved on retry without any source or tool change.
`deliver2.py Q65 lem-sfb-equivalence-square-inverse-mate-coherence --no-push`
then printed `OK (dry run)`: the preflight passes and both the sandbox module and
its actual library module compile cleanly, with the expected postponed proofs only.
The overlay also compiled both recorded non-public proof dependency modules.

A final source audit confirms: only `lean` changes in the node; the recorded main
signature matches the file verbatim; all 16 universes are explicitly bound;
there are exactly three theorems and three `sorry` proofs; maximum Lean line width
is 89 characters. All compilation was through the prescribed wrappers. Nothing
in the shared read-only clone was edited directly.

## Second reading by Q65

A separate source-to-signature pass was performed by this dispatched worker.
No additional agent was started, as expressly required by the dispatch brief;
the maintainer's independent delivery review remains the independent reading.

Reopened the node and the entire delivered module. Matched every row above back
to the exact binders and conclusions. In particular, the uniqueness quantifier
requires only mate normalization; the full Hom assertion quantifies over every f;
the primed instance is the unrestricted first theorem applied to the other four
categories; and clauses (2) and (3) assume exactly that normalization of their
specified comparisons.

Checked the routes' endpoints independently. `hdelta` goes from
E0(R10(R21 Z)) to Rb20(E2 Z). The compositor conclusion goes from
E2(L12(L01 X)) to Lb02(E0 X). `hb` goes from EC(P(U Y)) to Ub'(Qb(EB Y)).
The inverse-mate conclusion goes from ED(J'(P X)) to Qb(Jb(EA X)).
The displayed factor order on each route agrees with functional composition in
the node. The conjugation in `ha` uses direct adjunction first, composite second,
so its codomain is R20 to R21⋙R10, exactly `delta.inv`. The barred case agrees.

Checked that each theorem has its complete corresponding natural-language proof,
that all three postponed proofs belong to this node, that no new notion is copied,
and that only `lean` changes in the node copy. Added a module-level list of the
three declarations and clarified the final proof's use of ED to reflect isomorphisms.
No mathematical mismatch or source correction was found in this pass.
