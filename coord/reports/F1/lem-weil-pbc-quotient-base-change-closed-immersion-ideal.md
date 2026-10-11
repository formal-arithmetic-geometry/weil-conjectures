## Worker report

The module `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal` states the node in four
named theorems, corresponding to its four numbered clauses. Every proof is `sorry`;
there are no new definitions or dependency modules. The node copy changes only `lean`.
The main recorded signature is verbatim from the first theorem; `lean.declarations`
records all four declarations that together render the node.

Sources read: the node and its eight proof steps, and the public Stacks pages
[01JU](https://stacks.math.columbia.edu/tag/01JU) (lemma-fibre-product-immersion),
[01IN](https://stacks.math.columbia.edu/tag/01IN) (lemma-closed-subspace-scheme),
[01I4](https://stacks.math.columbia.edu/tag/01I4) (lemma-fibre-product-affine-schemes),
[01JQ](https://stacks.math.columbia.edu/tag/01JQ) (lemma-fibre-product-affines), and
[088F](https://stacks.math.columbia.edu/tag/088F) (remark-reformulate-existence-theorem).
The local checkout contains only the literature lists, not the Stacks TeX, so these
pages were opened directly. The source gives the image ideal in 01JU (1), the
quotient description on affine opens in 01IN, the tensor-product description in
01I4/01JQ, and the quotient-base-change system in 088F. Clauses (2)-(4) are the
agent's affine consequences specified in this node, not extra claims of 01JU.

Hypotheses and notation, common to the four declarations:

- The ring is `{A : Type u} [CommRing A]`, with no domain, field, Noetherian,
  characteristic, or nontriviality assumption. As throughout the scheme statements,
  “ring” here means commutative ring.
- `S = Spec A` is `Spec (CommRingCat.of A)`.
- The arbitrary scheme is `{X : Scheme.{u}}`; its specified structure morphism is
  `(f : X ⟶ Spec (CommRingCat.of A))`. No affineness of X is imposed.
- Ideals K, K', J, J', L are `Ideal A`. The only inclusion hypothesis is
  `(h : J ≤ J')` in clause (3), and the only exponent restriction is `1 ≤ m` in (2).
- `qSpec(K)` expands to `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))`.
  Thus `pullback f qSpec(K)` is precisely X_K. `j(f,K)` and `p(f,K)` expand to its
  first and second projections. Its map to S is `j(f,K) ≫ f`.
- `tilde(A,K)` expands to Mathlib's `Scheme.IdealSheafData.ofIdealTop` of
  `K.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`. The inverse of ΓSpecIso
  transports K from A to the global sections of Spec A, so this is the associated
  quasi-coherent ideal, rather than the ideal of an unrelated ring.
- `ext(A,K,f)` expands to `tilde(A,K).comap f`, exactly the recorded declaration
  of `def-nagata-extended-ideal`. Mathlib encodes pullback ideals through the kernel
  of the base-changed subscheme immersion; 01JU identifies this with the image ideal
  in the node. No alternative private image or pullback construction is introduced.
- `rho(A,f,U)` is the ring map A → Γ(X,U), namely ΓSpecIso inverse composed with
  `f.appLE ⊤ U le_top`. `K.map rho(A,f,U)` is exactly KB (ideal extension).
- `W(f,K,U)` is `j(f,K) ⁻¹ᵁ U`; all seven local notations merely expand existing terms.
  `quotPrecheck false` allows field projections in notation quotations in the pinned
  Lean version; it does not change mathematical elaboration. `autoImplicit false`
  explicitly forbids unbound implicit parameters.

Clause-by-clause correspondence:

1. `AlgebraicGeometry.quotientBaseChange_closedImmersion_ideal` states
   `IsClosedImmersion j(f,K)` and `(j(f,K)).ker = ext(A,K,f)`. For every affine
   open `U : X.affineOpens`, it states `IsAffineOpen W(f,K,U.1)` and
   `(ext(A,K,f)).ideal U = K.map rho(A,f,U.1)`, rendering (K O_X)(U) = KB.
   The existential `e` is an isomorphism from the actual preimage open scheme to
   `Spec (Γ(X,U) ⧸ K.map rho(A,f,U))`. The equation
   `e.hom ≫ qSpec(K.map rho(A,f,U.1)) ≫ U.2.isoSpec.inv = j(f,K) ∣_ U.1`
   says it identifies the actual restricted projection with the quotient morphism
   over U, using U's canonical affine-spectrum isomorphism. This is compatibility
   of the morphism, not merely an isomorphism of the underlying schemes.

2. `AlgebraicGeometry.quotientBaseChange_extendedIdeal_mul_pow` quantifies over both
   K and K' and states `ext(A,K,f) * ext(A,K',f) = ext(A,K * K',f)` in the
   Mathlib ideal-sheaf semiring. Its second conjunct states for every K and every
   `m : ℕ` with `1 ≤ m` that `ext(A,K,f) ^ m = ext(A,K ^ m,f)`.
   Neither the excluded exponent m = 0 nor any restriction on ideals is added.

3. `AlgebraicGeometry.quotientBaseChange_nestedIdeals` assumes just `J ≤ J'`.
   It supplies a morphism `i : pullback f qSpec(J') ⟶ pullback f qSpec(J)`.
   Its first two equations are `i ≫ j(f,J) = j(f,J')` and
   `i ≫ p(f,J) = p(f,J') ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))`.
   The subsequent universal quantifier over `i'` says these same two identities
   uniquely determine i, independently of its further properties.
   Next are `IsClosedImmersion i` and `i.ker = ext(A,J',j(f,J) ≫ f)`, with J'
   extended along X_J → S, as required, not only along X_J → Spec(A/J).
   For each original affine U there are isomorphisms e, e' to Spec(B/JB) and
   Spec(B/J'B). Both satisfy the quotient-projection equation of (1).
   The final equation uses `Ideal.Quotient.factor (Ideal.map_mono h)` and says
   that the transition i on these opens is the Spec of B/JB → B/J'B.
   It is written after the open inclusion into X_J; that inclusion is a mono,
   so this is precisely the equation of restricted morphisms. This avoids a
   redundant proof argument asserting the equality of the two preimage opens.

4. `AlgebraicGeometry.quotientBaseChange_extendedIdeal_comap` states
   `(ext(A,L,f)).comap j(f,K) = ext(A,L,j(f,K) ≫ f)` for every K and L.
   For every affine U it supplies the affineness proof hW for its preimage and
   states separately that the sections of each of these two ideal sheaves on W
   equal `(L.map rho(A,f,U.1)).map ((j(f,K)).app U.1).hom`.
   This is LB extended along the sections map B → Γ(X_K,W); under the compatible
   quotient identification of (1), it is L · (B/KB). Both ideals are explicitly
   computed, not merely declared equal with no local computation.

Dependency declarations read and used:

- `def-pc-scheme` and `def-weil-affine-spectrum`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `AlgebraicGeometry.Spec`, and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; read signatures and docstrings at lines
  35-77 and 469-480. ΓSpecIso at lines 594-620 gives the global-section identification.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  read lines 93-116. The imports of Functorial supply the scheme pullbacks.
- `def-nagata-extended-ideal`: `AlgebraicGeometry.Scheme.IdealSheafData.comap` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`, lines 38-41. Read the full
  module, including comap_comp and ker_fst_of_isClosedImmersion.
- `def-weil-closed-immersion`, a Mathlib leaf: `AlgebraicGeometry.IsClosedImmersion`
  in `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, lines 42-47. Its
  recorded `mathlib_match` is used; no replacement lean record is required.
- `def-sbc-closed-immersion-ideal-sheaf`: `AlgebraicGeometry.Scheme.Hom.ker` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, lines 689-705. Its definition uses
  the largest quasi-coherent subideal of the componentwise kernel, and
  `ker_apply` computes the literal componentwise kernel for quasi-compact maps,
  as all the closed immersions here are.
- `def-sbc-ideal-sheaf-powers`: `AlgebraicGeometry.Scheme.IdealSheafData`, with
  its `Mul` and `Pow` instances and `ideal_mul`/`ideal_pow`, in the same Basic
  module. Read the structure at lines 55-76 and the semiring formulas at 422-450.
  Its `ofIdealTop` (lines 464-475) provides the associated ideal used above.

Only `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` is imported; it supplies all
these declarations transitively and is used directly for comap.

Edge cases checked mathematically before finalizing the statement:

- K = 0 gives X_K ≅ X, zero kernel, and B/0 ≅ B. K = A gives the empty
  X_K and the unit ideal on X. Empty schemes and empty affine opens are included;
  the zero ring and its spectrum are allowed by `[CommRing A]`.
- J = J' makes the transition an isomorphism and its ideal zero on X_J;
  extending J' to X_J indeed gives zero. J = 0 and J' = A give respectively
  the base scheme and the empty terminal quotient cases. The quotient factor
  direction is from the smaller ideal to the larger ideal, contravariant for Spec.
- L = 0 and L = A give zero and unit ideals on both sides of (4), including
  when X_K is empty. No flatness hypothesis on f or on the quotient is needed.
- The exponent range includes m = 1 exactly as the node specifies. Product
  identities allow zero and unit ideals. All characteristics are allowed.
- A and X use the same arbitrary universe u, the standard Scheme/Spec universe
  convention; choosing u large enough covers any ring and scheme in the node.
  No quantified test objects have a smaller independent universe.

Searches actually run for this item:

- `msearch.py leansearch`, query “base change Spec quotient ring ideal sheaf affine
  open quotient product ideals”: HTTP Internal Server Error, recorded as unavailable,
  not as no match.
- `msearch.py leanfinder`, query “Base change of Spec(A/K) to a scheme X is a closed
  immersion with ideal K O_X and affine ring B/KB”: eight hits, including
  IsClosedImmersion.Spec_iff, spec_of_quotient_mk, isStableUnderBaseChange, and
  spec_of_surjective. These give ingredients, not all four clauses of the node.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.IdealSheafData.comap, AlgebraicGeometry.Scheme.IdealSheafData.ideal`:
  one hit, ideal_comap_of_isOpenImmersion, which concerns open immersions, not this
  affine quotient computation and the remaining clauses.
- `msearch.py grep`, query `ideal_comap|ker_fst|ofIdealTop|quotient` in
  `AlgebraicGeometry/IdealSheaf`: 13 hits, including ofIdealTop,
  ker_fst_of_isClosedImmersion, and ideal_comap_of_isOpenImmersion; no full match.
- `rg` of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf` for `ofIdealTop|quotient.*base|quotientBase|quotient-base-change`:
  existing associated-ideal uses, tensor-quotient lemmas, and citers of this item;
  no existing declaration of this four-clause statement.
- `rg` for the item id and `quotientBaseChangeIdeal` in the upstream names table
  and WeilConjectures: no hits. The source searches by the item id returned no
  upstream attachment. Searches for the exact new declaration names found none.

No statement correction or disputed statement is needed. The local definitions of
Scheme, Spec, pullback, kernel, extended ideal, products and powers are used exactly
as their dependency records specify. Docstrings include all eight proof steps and
name their non-elementary supporting nodes for stage 3.

Validation: server `scompile.py` compiled the final module in 2.6 seconds with no
errors or warnings. `deliver2.py --no-push` printed OK: the commit compiles and
passes preflight except for the independent second reading, which the second reader
will write before delivery. Nothing was pushed.


## Second reading by F1

I independently read the item node (including all eight proof steps), its sandbox
copy and the four declarations in QuotientBaseChangeIdeal.lean. I read every
statement dependency and the recorded Mathlib signatures in Scheme.lean,
HasPullback.lean, IdealSheaf/Basic.lean, IdealSheaf/Functorial.lean and
Morphisms/ClosedImmersion.lean. No new nodes, dependency modules, or statement
correction are present, so H12/H13 and the corrected-statement citer checks do
not apply.

Source check: the local literature checkout does not contain Stacks TeX. I read
schemes.tex and coherent.tex directly from the Stacks Project GitHub raw source,
at labels lemma-fibre-product-immersion, lemma-fibre-product-affine-schemes,
lemma-fibre-product-affines, lemma-closed-subspace-scheme and
remark-reformulate-existence-theorem. I also opened the official pages
https://stacks.math.columbia.edu/tag/01JU,
https://stacks.math.columbia.edu/tag/01I4,
https://stacks.math.columbia.edu/tag/01JQ,
https://stacks.math.columbia.edu/tag/01IN and
https://stacks.math.columbia.edu/tag/088F.
01JU assumes arbitrary morphisms of schemes and a closed immersion; 01IN
assumes only a scheme and a closed immersion of locally ringed spaces. 01I4
assumes ring maps, and 01JQ affineness of the three schemes in that local
calculation. None requires flatness, Noetherianity, a field, or finite type.
088F has Noetherian completeness and separated finite type hypotheses for the
existence theorem application; those are not hypotheses of this general
quotient-base-change lemma assembled from 01JU and the affine calculations.

Node objects, hypotheses, and conclusions matched individually:

- A is a commutative ring: `{A : Type u} [CommRing A]` in every theorem.
  Verdict: exact; in particular no nontriviality, domain, field, characteristic,
  Noetherian, completeness or finiteness hypothesis.
- S is Spec A: `Spec (CommRingCat.of A)`. X is an arbitrary scheme with a
  specified map f to S: `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))`.
  Verdict: exact. X itself is not assumed affine, separated, or flat.
- K and all the other ideals are `Ideal A`. X_K is
  `pullback f qSpec(K)`; `j(f,K)` and `p(f,K)` are its actual first and second
  projections. `qSpec(K)` is Spec of `Ideal.Quotient.mk K`.
  The map X_K to S is `j(f,K) ≫ f`. Verdict: exact, with Spec contravariance
  and composition order checked.
- The associated ideal tilde K is `tilde(A,K)`, namely `ofIdealTop` after
  mapping K through `(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`.
  I checked the inverse direction: Gamma Spec A → A is the forward map, so
  its inverse correctly transports K into Gamma Spec A. `ofIdealTop` then
  restricts that ideal to affine opens, giving the associated ideal sheaf.
- The image ideal K O_X is `ext(A,K,f)`, exactly that associated ideal's
  recorded `IdealSheafData.comap f`. This is not a private tensor pullback.
  Functorial.lean defines comap as the kernel of the base-changed subscheme
  immersion, the same image ideal described by 01JU. Verdict: exact use of
  def-nagata-extended-ideal. Its quasi-coherence is included in the
  IdealSheafData type.
- For an arbitrary affine open, `U : X.affineOpens`, B is `Γ(X,U.1)`;
  `rho(A,f,U.1)` is A → Gamma Spec A → Gamma(X,U), and `K.map rho(...)`
  is KB. `W(f,K,U.1)` is the actual inverse-image open. Verdict: exact.
- Clause (1), first conclusion: `IsClosedImmersion j(f,K)` and
  `(j(f,K)).ker = ext(A,K,f)`. I checked `IsClosedImmersion` is a closed
  embedding with surjective stalk maps, and `Hom.ker` computes the ordinary
  sections kernel for quasi-compact maps, including closed immersions.
  Verdict: the required immersion and ideal equality, with no extra premise.
- Clause (1), local conclusions: for every affine U, `IsAffineOpen W(...)`
  and `(ext(...)).ideal U = K.map rho(...)`. The existential e identifies
  the actual preimage scheme with Spec(B/KB), and
  `e.hom ≫ qSpec(K.map rho(...)) ≫ U.2.isoSpec.inv = j(f,K) ∣_ U.1`
  identifies the morphism over U as well. Verdict: every local clause is
  present; the isomorphism is compatible with projection, not only abstract.
- Clause (2): `∀ K K' : Ideal A` followed by the product equality, and
  `∀ (K : Ideal A) (m : ℕ), 1 ≤ m → ...` followed by the power equality.
  Basic.lean's multiplication and powers are pointwise multiplication and
  powers of affine ideals, exactly def-sbc-ideal-sheaf-powers.
  Verdict: both clauses exact; the only exponent restriction is the node's.
- Clause (3), sole inclusion hypothesis: `(J J' : Ideal A) (h : J ≤ J')`.
  The existential i has source X_Jprime and target X_J. Its first equation
  is `i ≫ j(f,J) = j(f,J')`; the second uses
  `p(f,J') ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))`.
  The following universal i' condition asserts uniqueness for exactly these
  two projection identities. Verdict: the same universal-property morphism,
  with the ring map A/J → A/Jprime pointing in the correct direction.
- Clause (3), geometric conclusions: `IsClosedImmersion i` and
  `i.ker = ext(A,J',j(f,J) ≫ f)` extend Jprime along X_J → Spec A.
  For every affine U, e and eprime identify W_J and W_Jprime with
  Spec(B/JB) and Spec(B/Jprime B), both over U. The final equation uses
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono h)))`
  between those spectra, and then the inclusion of W_J into X_J.
  Verdict: exactly the asserted local quotient transition. Composing with
  this open inclusion loses no information, since it is a monomorphism.
- Clause (4), global conclusion: `(ext(A,L,f)).comap j(f,K) =
  ext(A,L,j(f,K) ≫ f)`, with arbitrary K,L. Verdict: the specified image
  under j_K equals L extended along X_K → S.
- Clause (4), local conclusion: for every affine U, an affineness proof hW
  is supplied and the sections of each of the two ideals on W are separately
  equal to `(L.map rho(A,f,U.1)).map ((j(f,K)).app U.1).hom`.
  Verdict: these are LB extended along B → Gamma(X_K,W); under clause (1)'s
  compatible quotient identification, both are L(B/KB). There is no omitted
  local computation or choice of an unrelated quotient algebra.

Edge cases: A may be the zero ring; X or U may be empty; K may be zero or
unit. They give respectively the whole scheme or the empty closed subscheme,
with zero or unit ideal; all binders still apply. J = Jprime gives the
identity transition and zero extended Jprime on X_J; J = 0 and Jprime = top
are included. L = 0 and L = top give zero and unit extended ideals. No
index set is used, so an empty index set is not an additional case. m = 1
is included, m = 0 is excluded exactly as in the node. No characteristic
is excluded. The arbitrary common universe u is Mathlib's Scheme/Spec
convention: the ring and scheme may be placed together in any sufficiently
large universe; there is no quantifier over test objects in a smaller
independent universe and no smallness premise. `autoImplicit false` and
`universe u` bind all variables explicitly.

Independent searches (different wording from the worker, via msearch.py):

- LeanFinder: “For ideals J contained in Jprime, the quotient base changes
  X_Jprime to X_J form a closed immersion with ideal Jprime O_X_J”. Eight
  hits, including IsClosedImmersion.Spec_iff, spec_of_quotient_mk,
  instIsClosedImmersionInclusion, subschemeMap and base-change stability.
  These are ingredients or different subscheme presentations, not this
  four-clause statement with its local identifications.
- Loogle: `AlgebraicGeometry.Scheme.IdealSheafData.comap, HMul.hMul`.
  Zero hits, so no existing product-extension statement found.
- Grep: `comap_mul|comap_pow|comap_comp|ker_fst_of_isClosedImmersion`.
  The broad query returned mostly unrelated comaps; I therefore searched
  `comap_mul|comap_pow|comap_comp|ker_fst_of_isClosedImmersion|ideal_comap`
  specifically in AlgebraicGeometry/IdealSheaf. Six hits, containing the
  existing comap_comp and kernel-of-base-change result. I opened both.
  comap_comp gives the global equality in clause (4), but does not give
  that clause's two affine computations, and neither states the whole node.
- Direct rg in WeilConjectures and project lean/Sheaf for
  `comap_mul|comap_pow|quotient.*[Ii]deal|nested.*[Ii]deal|extended.*[Ii]deal`
  found algebraic ingredients and the modules FirstOrderThickeningBaseChange
  and IdealTimesQuasiCoherentAffineSections. I read those: the first cites
  this node and concerns square-zero thickenings, the second ideal-module
  products, not these quotient-base-change clauses.
- Exact searches for all four proposed full declaration names in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found none.
  No notion is newly defined: all local notations expand dependency or
  Mathlib declarations. No missing dependency requires a new node or module.

Mismatch and repair verdict: none found. I left the correct Lean module and
node record unchanged, and added only this independent second reading.
The module and theorem docstrings name the source and blueprint item; their
proof paragraphs cover steps (1)-(8) with the cited supporting nodes.
There are four named theorem sorries, no other proof or hollow definition,
no new private notion, and no unused or nonstandard import. The one import
is directly used for comap and supplies the other required constructions.
I checked the node's lean.statement byte-for-byte against the first signature,
the four names against lean.declarations, and every line against the
100-character limit. The server single-file compile succeeded in 2.6 seconds
with no errors or warnings. No unit statement is affected.
