## Worker report

Module: `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents`.
Main declaration: `CategoryTheory.RingedSiteBoundedDual.boundedDualComponents`.
Stage 2 only: the sole postponed proof is this named theorem, with the node's six-step
natural-language proof in its docstring. All helper data are explicit applications of existing
constructions. No statement correction, new definition node, or dependency repair was needed.

Source read: `literature/stacks-project/sites-cohomology.tex`, Section 0A8X
`section-hom-complexes`, and Tag 08JJ `lemma-dual-perfect-complex`, second proof paragraph.
The source identifies the terms and says evaluation is given up to sign; expansion of the
Section 0A8X differential gives the precise signs stated in this node.

Hypothesis and clause correspondence (names below are in `CategoryTheory.RingedSiteBoundedDual`):

- Small ringed site with commutative coefficients: `{C : Type c} [Category.{v} C]`,
  `{J : GrothendieckTopology C}`, and `R : Sheaf J CommRingCat.{max c v r}`.
  `J.HasSheafCompose` is the standard coefficient-forgetful composition interface needed by
  the recorded declarations. There is no sheafification, exactness, projectivity, finite-free,
  derived-category or reflexivity assumption. The site object and morphism universes are
  independent. `max c v r` is the chosen ambient universe of def-weil-size-convention;
  it contains the site and coefficients and is closed under these internal Homs.
- Cochain complex: `E : CochainComplex (Modules R) ℤ`. `Modules` transparently abbreviates
  the existing `SheafOfModules` category, not a new module-sheaf definition.
- Integers a,b and the precise bound: `(a b : ℤ)` and
  `hE : ∀ i, i < a ∨ b < i → IsZero (E.X i)`. No `a ≤ b` is assumed.
- O=R[0]: `coefficient` abbreviates `SheafOfModules.unit`; `zeroComplex` abbreviates
  the standard `CochainComplex.singleFunctor` applied to that object in degree zero.
  `modulesHasZeroObject` supplies the standard structure directly from Mathlib's
  `hasZeroObject_of_hasTerminal_object` and the existing limits instance. This is real
  structure from an existing theorem, with no postponed proof and no local instance.
- D=Hom(E,O), D'=Hom(D,O), and T^vee: `complexDual R E`, its second iteration, and
  `dual R T` unfold directly to the recorded `CategoryTheory.homComplex` and
  `SheafOfModules.homObj`.
- Canonical D^q ≅ (E^(-q))^vee: `α p q h` for `h : p+q=0`.
  Conjunct 1 sets its hom to `component`, which is precisely `homComplexπ` followed
  by `homObjMap` of the standard `singleObjXSelf` degree-zero identification.
  The more flexible p,q indexing avoids hidden transports; taking p=-q gives the node.
- Canonical (D')^i ≅ ((E^i)^vee)^vee: `γ i`. Conjunct 2 says that its composite with
  precomposition by `(α i (-i) _).hom` equals the same canonical projection for D.
  This uniquely fixes the iterated identification, including the double-negated index.
- Dual differential formula: conjunct 3 is the commutative transported-differential square
  with `(q+1).negOnePow • homObjMap (E.d (-(q+1)) (-q)) (𝟙 coefficient)`.
  `-(q+1) = -q-1`, and `Int.negOnePow` expresses the integer sign (-1)^(q+1).
- Bidual differential formula: conjunct 4 is
  `d_D' ≫ γ = -(γ ≫ homObjMap (homObjMap d_E id) id)`.
  The inner and outer Hom maps are respectively the transpose and double transpose.
- Reversed bound: conjunct 5 is `q < -b ∨ -a < q → IsZero ((complexDual R E).X q)`.
- Ordinary evaluation: `δ i : E.X i ⟶ dual R (dual R (E.X i))` and conjunct 6 give
  its value on every U-section x, every slice object W, and every local functional φ:
  evaluate φ at the restriction of x, using the identity object of the further slice.
  These are actual sheaf morphisms, not global-section-only functions.
- The homogeneous formula defines a chain map: `β : E ⟶ complexDual R (complexDual R E)`
  is a morphism of cochain complexes, hence includes the chain-map identity. Conjunct 7
  gives its homogeneous formula using the actual product projections, on every slice,
  for arbitrary i,q,t with i+q=t and q+i=t. It is exactly `(i*q).negOnePow • φ(x)`;
  nonzero target degree t is included, so zero coefficient factors are not discarded.
- Its degree-i component is (-1)^i δ: conjunct 8 states
  `β.f i ≫ (γ i).hom = i.negOnePow • δ i`.
- Arbitrary bounded E without finite-free retract or exactness: E has no further hypotheses.
  No invertibility of δ or β is asserted.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention record; realized by the explicit
  independent site universes c,v and ambient max c v r, with every level bound explicitly.
- `def-pur-hom-complex`: `WeilConjectures.Algebra.Homology.HomComplex`,
  `CategoryTheory.homComplex` (and its chosen product bifunctor).
- `def-pur-sheaf-hom`: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj` and `homObjMap`. These are the actual localized-sheaf Hom objects.
- Added existing landed statement dependency `lem-sc-hom-complex-projections`:
  `WeilConjectures.Algebra.Homology.HomComplexProjections`,
  `CategoryTheory.homComplex_projections_exists`, accessed by the public API
  `CategoryTheory.homComplexπ` in `WeilConjectures.Algebra.Homology.HomComplexComponents`.
  Its full product-limit, differential, and functoriality signature and docstring were read.
  The imported Components module publicly imports Projections and HomComplex; HomComplex
  publicly imports InternalHom, so all original statement/proof dependencies are imported.
- Mathlib `SheafOfModules.unit`, `CochainComplex.singleFunctor`,
  `HomologicalComplex.singleObjXSelf`, the module-sheaf limits, and
  `CategoryTheory.Limits.hasZeroObject_of_hasTerminal_object` provide R[0] and its standard
  degree-zero projection target. There is no new independent notion in the helper aliases.

Edge cases checked mathematically before the statement was written:

- Empty site, zero ring, zero sheaves and zero complexes: every formula is an identity of
  the available sheaf morphisms. No nonempty, nontrivial, or characteristic assumption occurs.
- a>b forces all terms zero; both the assumed bound and reversed interval still express this.
- a=b=0 and E concentrated in degree zero: β is ordinary evaluation with sign +1.
- Odd and negative degrees: parity of -i*i equals parity of i. Thus β has sign -1 in
  every odd degree. The consecutive signs in the twice-dual differential multiply to -1.
- Two-term complexes with a nonzero differential (for example Z --2--> Z in degrees 0,1):
  the bidual differential is its negative and β has components +δ,-δ, so the chain square
  commutes. The statement does not accidentally assert an unsigned bidual chain map.
- Characteristic two: all signs reduce to +1, consistently on both sides.
- Nonreflexive or nonprojective terms: δ is specified by evaluation and is not claimed
  invertible. No termwise exactness is inferred or assumed.
- Site objects in Type (u+1) and morphisms in Type u remain admitted; no c=v equality is used.

Searches for existing declarations (2026-10-21):

- `msearch.py ... leanfinder`, query "The internal sheaf Hom complex dual into a ring in
  degree zero has reversed terms and signed bidual evaluation": OK 8 hits, generic sheaf
  cohomology, sheaf Hom sections and module units; no matching bounded signed dual theorem.
- `msearch.py ... loogle`, query `CochainComplex, Module.Dual`: OK 0 hits.
- `msearch.py ... grep`, query `homComplex.*(dual|single)|bidual|doubleDual`, restricted
  to `Algebra/Homology`: OK 0 hits in Mathlib.
- `msearch.py ... leansearch`, query "Internal sheaf Hom complex to the coefficient sheaf
  in degree zero has dual terms with reversed indices and signed evaluation to the double dual":
  OK 8 hits. The HomComplex hits are the external additive-group Hom complex; the other hits
  concern opposite complexes. None states internal module-sheaf dual components and bidual signs.
- `rg` on `lean/WeilConjectures/Algebra` and `lean/Sheaf` for dual/bidual/component names
  found `HomComplexToSingle`, `HomComplexComponents`, `Sheaf/Bidual`,
  `RingedSiteDualityMaps`, and `HomFiniteProjective`; their relevant declarations and
  docstrings were opened. ToSingle gives only the first-dual complex identification and
  identifies site object, morphism and coefficient universes; Bidual has the same universe
  restriction and treats a single sheaf. DualityMaps supplies the signed evaluation chain map
  but not the component identifications, differential identities, or reversed support bound.
  HomFiniteProjective supplies ordinary evaluation, not this bounded-complex theorem.
  The present statement uses the general-universe HomComplex and Hom API directly and pins
  evaluation by its local formula, introducing no competing canonical choice definition.
- `rg` for `boundedDualComponents`, `namespace CategoryTheory.RingedSiteBoundedDual`,
  and `bounded.*dual.*components` in `lean/WeilConjectures` and `lean/Sheaf`: no hit.
- `grep -rn lem-sfb-ringed-site-bounded-dual-components lean/WeilConjectures`: no hit.
- `rg` for the proposed namespace/name in `dag/lean_names_upstream.json` and Mathlib
  `Algebra/Homology`: no hit. There is no maintenance repair note for this item.

Validation: prescribed `scompile.py NH lem-sfb-ringed-site-bounded-dual-components <module>`
compiled both its sandbox form (12.9 s) and actual library module (28.3 s), exit 0 with no
messages. Earlier elaboration issues were repaired by explicit universe arguments and the
standard zero-object structure; no universe restriction or mathematical hypothesis was added.

## Second reading by NH

No second reading by another worker: the dispatcher brief forbids starting other agents.
The maintainer's independent review reads the delivery. Self-review checked the node and module
clause by clause above, especially the contravariance direction of the γ projection square,
the minus sign on the double transpose, and the full homogeneous formula at nonzero target degree.
