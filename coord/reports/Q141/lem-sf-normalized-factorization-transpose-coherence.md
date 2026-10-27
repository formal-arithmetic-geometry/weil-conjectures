## Worker report

The module `Sheaf.CategoryTheory.NormalizedFactorizationTransposeCoherence` states
`CategoryTheory.normalized_factorization_transpose`,
`CategoryTheory.normalized_factorization_transpose_identity`, and
`CategoryTheory.normalized_factorization_transpose_comp`. All three proofs are `sorry`;
there are no new definitions. Together these declarations state the entire node.
The node is unchanged except for its `lean` record. No statement correction, dependency
repair, new DAG node, or disputed statement is needed.

The source was read in the current blueprint:
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`,
second paragraph, and in `literature/stacks-project/categories.tex`,
`definition-adjoint` (0037) and `lemma-transformation-between-functors-and-adjoints` (0B65).
The node's six-step categorical argument expands that blueprint comparison.

Hypothesis and clause correspondence for `normalized_factorization_transpose`:

| Node | Lean |
| --- | --- |
| Four categories A, B, P, Q | Four explicit `Type` binders and four `Category` instances, with independent object and morphism universes |
| C_S and C_T | `CS : A ⥤ P`, `CT : B ⥤ Q` |
| F_e, F'_e, E_e, F_p, F'_p, E_p | Functor binders `Fe Fe' Ee` and `Fp Fp' Ep` |
| Common R and two pro-etale right adjoints | `R : B ⥤ A`, `J J' : Q ⥤ P` |
| Specified adjunctions | `ae`, `ap`, `ap'`; the fourth is explicitly `ae.ofNatIsoLeft re` throughout, exactly the stipulated transported adjunction |
| Global left changes | `re : Fe ≅ Fe'`, `rp : Fp ≅ Fp'` |
| t is the conjugate of inverse r_p | The exact expression `conjugateIsoEquiv ap ap' rp.symm`; no arbitrary right comparison is supplied |
| Full subcategory A_0 | `A0 : ObjectProperty A` and Mathlib's `A0.FullSubcategory`, with inclusion `A0.ι` |
| Delta, Delta', B on A_0 | `delta`, `delta'`, `closure`, natural isomorphisms of the restricted composite functors |
| Closure comparisons on A_0 | `qe`, `qe'`, `qp`, `qp'` are natural isomorphisms after restriction. The p-side is restricted along `A0.ι ⋙ CS`, so no extension to every object of P is required |
| First displayed comparison square | `hsquare`, for every object of the full subcategory |
| Two displayed closure squares | `hclosure`, `hclosure'` |
| q'_p r_p = q_p | `hqp`, componentwise on the same full subcategory |
| Injectivity on just Hom(F_e L,E_e L) | `hinj`, with the domain of `CT.map` explicitly annotated; no `[CT.Faithful]` |
| q'_e r_e = q_e | First conclusion, for every `L : A0.FullSubcategory` |
| Arbitrary h and h_0, satisfying h Delta = C_T(h_0) | Second conclusion quantifies `L M h h0` and then takes precisely that equality as an implication premise |
| h' = h r_p inverse, h'_0 = h_0 r_e inverse | Expanded directly as `rp.inv.app (CS.obj L.obj) ≫ h` and `re.inv.app L.obj ≫ h0`; no opaque auxiliary maps or statement-level lets |
| h' Delta' = C_T(h'_0) | First conjunct of the second conclusion |
| Equality of etale transposes | Second conjunct, using the transported adjunction's `homEquiv` and `ae.homEquiv` |
| Pro-etale transpose changes by t | Third conjunct, using `ap'.homEquiv`, `ap.homEquiv`, and the specified conjugate's component at `CT.obj M` |
| Equality of normalized closure arrows | Fourth conjunct, using `qp'.inv.app L` and `qp.inv.app L` |
| M with H = R M in A_0 | Third conclusion quantifies `M` and `hH : A0 (R.obj M)`; its subcategory object is exactly `⟨R.obj M, hH⟩` |
| Two isomorphisms gamma and gamma' | Explicit isomorphism binders with source `CS.obj (R.obj M)` and the two specified right-adjoint targets |
| Two normalized counit equations | The two implication premises in the third conclusion, using respectively `ae.counit` and `(ae.ofNatIsoLeft re).counit` |
| gamma' = t gamma | First conjunct after those premises, as equality of hom morphisms of the supplied isomorphisms |
| Arbitrary W and rho, theta = rho gamma inverse, theta' = rho gamma' inverse | Explicit `∀ (W : P) (rho : CS.obj (R.obj M) ≅ W)` and the expanded composites of `gamma.inv`, `gamma'.inv`, and the same `rho.hom` |
| theta' t = theta | Final equality, with diagrammatic composition in Lean |

All formulas reverse the node's written right-to-left multiplication into Lean's `≫` order.
In particular the left side of the final equality begins with t, then gamma' inverse, then rho.
The node's natural isomorphisms said to be "on A_0" are supplied exactly on that full
subcategory; global isomorphisms can of course be restricted to supply them.

The final identity/composition sentence is made explicit by the other two declarations:

- `normalized_factorization_transpose_identity` states that left-adjunction transport by
  `Iso.refl` fixes the specified adjunction; conjugation of `Iso.refl Fp` is `Iso.refl J`;
  both transported arrows are unchanged; gamma and its inverse followed by arbitrary rho
  are unchanged. Closure-square and transpose conclusions for identity changes are the
  corresponding specializations of the first theorem.
- `normalized_factorization_transpose_comp` supplies a third pair `Fe''`, `Fp''`, right
  adjoint `J''` with specified `ap''`, and successive natural isomorphisms `se`, `sp`.
  Its two `hsquare` premises are the successive comparison squares. Its `hqp` premises
  are the two p-side normalizations. Its `hqe` premises are precisely the two e-side
  conclusions already supplied by the first theorem (not additional requirements on the
  original node's data). All three closure isomorphisms target the same `Ee`, `Ep`.
  The first conclusion gives the composite square and both composite closure normalizations.
  The next gives equality of successive and direct adjunction transport. The next gives
  the conjugate cocycle `t ≪≫ u = conjugate(composite inverse)`. The next supplies the
  two successive-versus-direct arrow identities, the etale and pro-etale composite
  transpose identities, and the composite normalized closure-arrow identity. Applying
  the first theorem with the composite square gives its h'' Delta'' square as well.
  The last conclusion takes the two gamma transport identities supplied by the first
  theorem for normalized counit solutions and asserts the direct composite gamma identity,
  theta'' u = theta', and theta'' (u t) = theta, for every W and the same arbitrary rho.
  Thus all normalized solutions, squares and transpose comparisons respect composition;
  the second theorem supplies the identity case.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Category.Basic`: `CategoryTheory.Category`, the exact
  `def-nagata-category` match; both composition laws and associativity were read.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction.mkOfHomEquiv`,
  its `CoreHomEquiv` argument and full construction, `Adjunction.homEquiv`,
  `Adjunction.homEquiv_unit`, `Adjunction.homEquiv_counit`, `Adjunction.ofNatIsoLeft`,
  and `Adjunction.homEquiv_ofNatIsoLeft_apply` were read. The statements use the
  specified adjunctions and their Hom bijections, not replacement bijections.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.conjugateEquiv`,
  `conjugateEquiv_counit`, `conjugateEquiv_comp`, `conjugateEquiv_id`, and
  `conjugateIsoEquiv` were read, including the direction of the equivalence and
  the real isomorphism construction. `conjugateIsoEquiv` is used in every t formula.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: `ObjectProperty.FullSubcategory`
  and `ObjectProperty.ι` provide the existing full-subcategory construction.
- `Sheaf.CategoryTheory.CoherentRightAdjointComparisons` is imported privately for
  the proof dependency `CategoryTheory.exists_unique_coherent_right_adjoint_comparisons`;
  its entire signature and proof docstring were read. The other proof dependencies
  are already in the public Mathlib imports. No dependency interface is repaired.

Edge cases checked before writing and on the final signatures:

- A_0 may be empty. Its natural isomorphisms, square premises and conclusions are empty
  families; the counit conclusion requires an actual membership proof, so is not
  accidentally asserted at an object outside A_0. Neither nonemptiness nor closure
  of A_0 under R is assumed.
- Object and morphism universes of all four categories are separate and explicit;
  all functors are between their specified categories. No equality of universes,
  smallness, finite objects, additive structure, or nonzero object is imposed.
- Identity left comparisons are covered explicitly. Successive comparisons use inverse
  components in the correct order, and the conjugate of the composite inverse has
  direction `J ⟶ J''`.
- The possibly nonfaithful CT needs injectivity only from `Fe.obj L.obj` to `Ee.obj L.obj`.
  The proof cancellation uses no other Hom set. All other clauses are ordinary
  adjunction identities and isomorphism cancellation.
- The counit source H is definitionally `R.obj M`; gamma and rho retain exactly this
  source, with no arbitrary replacement object or arbitrary comparison map.
- No extra case assumption on h, h0 or rho is used. All isomorphisms remain supplied
  data, and no existence theorem with sorry is used to select an object.

Searches for an existing declaration (all on 2026-10-22):

- `msearch.py ... leanfinder "Compatible changes of left adjoints preserve normalized
  factorization comparisons and conjugate their right adjoint transposes, coherently
  under composition and identity"`: eight hits, mainly `Adjunction.leftAdjointUniq_trans`
  and `leftAdjointCompIso`; no normalized-square/injectivity theorem.
- `msearch.py ... leansearch "Normalized closure comparisons commute with compatible
  changes of left adjoints and conjugate right adjoint transposes"`: eight hits including
  `conjugateEquiv_comm` and `conjugateIsoEquiv`, plus unrelated normal-closure declarations;
  no exact statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction.ofNatIsoLeft,
  CategoryTheory.conjugateIsoEquiv"`: service unavailable, HTTP 502. No no-match verdict
  is assigned to this unavailable search; the successful other searches supplied the API.
- `msearch.py ... grep "normalized.*factorization|conjugateIsoEquiv|homEquiv_ofNatIsoLeft"
  CategoryTheory`: 25 hits identifying the Mathlib conjugation and transport API,
  but not the combined theorem.
- `rg` over `lean/Sheaf` and `lean/WeilConjectures` for
  `normalized.*(factorization|transpose)|[Nn]ormalized[Ff]actorization|[Nn]ormalized.*[Cc]oherence`
  located the geometric specialization in `Sheaf.Paper.LocallyClosedRelativeTransposeNormalization`.
  Its actual factorization geometry and module-sheaf coefficients do not state this
  unrestricted four-category lemma; its refactor right comparison was read to check
  the inverse-r_p convention.
- `grep -rn "lem-sf-normalized-factorization-transpose-coherence" lean/WeilConjectures`
  gave no match. `rg` for the proposed declaration names in Mathlib CategoryTheory,
  upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` gave no existing declaration.

Validation: the prescribed `scompile.py Q141 lem-sf-normalized-factorization-transpose-coherence`
compiled this one delivered module in both sandbox and library modes against the live
published library, with no errors or warnings. `autoImplicit false` is explicit in the file.
No local compiler, global build, shared source mutation, or direct Git command was used.

## Second reading by Q141

The dispatcher explicitly forbids starting other agents. This section records a separate
in-thread rereading of the node and final file; it does not claim an independent agent
review. The maintainer's independent review follows delivery.

Reread all hypotheses and the eight displayed conclusions against the table above, then
checked the final identity/composition sentence against the two companion statements.
No mismatch was found. In particular checked inverse-r_p orientation, hH at R M,
restriction of natural isomorphisms to A_0, the absence of global faithfulness, the
transported rather than arbitrary etale adjunction, the use of the identical rho on both
sides, and the order of the successive inverse components. The composition theorem
uses the main theorem's e-normalizations and gamma transport conclusions as its premises,
so introduces no new requirement on the initial data. No changes were needed on rereading.
