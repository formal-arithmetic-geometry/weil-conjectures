## Worker report

This delivery states `AlgebraicGeometry.exists_projective_hilbert_polynomial_representation`
in `Sheaf.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability`. Its only theorem
has proof `sorry`. The definitions have complete data and no postponed proof.

The previous assignment ended when NV's stage-1 split landed. The retained sandbox contained
only dispatcher markers, with no Lean module, node copy, or report. I read the current reviewed
nine-step split and built this delivery from it. Its statement, proof, proof dependencies,
source, status and maintainer metadata are preserved verbatim. The only item fields changed
are `lean` and the addition of two definition dependencies to `stmt_deps`.

Hypothesis and clause correspondence:

- A Noetherian base in the explicitly stated sense is `S : Scheme.{u}` with
  `[IsLocallyNoetherian S] [CompactSpace S]`. The latter is quasi-compactness of the scheme,
  and is not a separation or finiteness hypothesis on the test schemes.
- The ambient scheme over S is `E : Over S`. Its specified projective embedding is
  `i : E.left ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)` with `[IsClosedImmersion i]` and
  `hi : i ≫ (ℙ(...) ↘ S) = E.hom`. `n : ℕ` includes n = 0; the lifted finite index type
  supplies exactly n+1 homogeneous coordinates at every scheme universe.
- The family functor is the already-published `properHilbertPresheaf E.hom`. It takes T to
  actual quasi-coherent ideals on `pullback E.hom T.hom`, with proper, flat, locally finitely
  presented quotient schemes. Its maps are `IdealSheafData.comap (baseChangeMap ... )`.
  Properness here imposes no extra restriction: a closed subscheme of the base change of
  the specified projective E is proper over T. Conversely properness supplies quasi-compactness
  and quasi-separatedness, making local finite presentation exactly finite presentation.
  Thus this is precisely the full functor in the item, including over non-Noetherian T;
  the upstream fixed-degree `hilbertPresheaf` would incorrectly restrict to finite fibres.
- `e : (properHilbertPresheaf E.hom).RepresentableBy H` is the natural representing
  equivalence, with `H : Over S`. Its `homEquiv` parametrizes all families, including
  families with different polynomials on different connected components of T.
- `HP : NumericalHilbertPolynomial → Over S`, `ι : ∀ P, HP P ⟶ H`, and
  `Nonempty (IsColimit (Cofan.mk H ι))` express H as the disjoint union of the HP over S.
  Colimits of this discrete diagram in the over category are the scheme coproduct with
  its structure morphism. This is an actual colimit cocone, not just a cover of points.
- A numerical polynomial is a rational polynomial integer-valued on all integers.
  Requiring integer values on all integers is equivalent to eventual integer values:
  finite differences propagate integrality backwards. In particular it includes every
  homogeneous-coordinate Hilbert polynomial. Nonrealizable numerical polynomials are
  retained, with empty components. Zero is included; no positivity predicate is imposed.
- Fibre-polynomial membership is `HasProjectiveFibreHilbertPolynomial E.hom i T
  (e.homEquiv k).1 P.1`. It quantifies over every point t of T and requires eventual equality
  of P(m) with the Euler characteristic of O(m) on the residue-field fibre. These are proper
  finite-type fibres over fields, and O(m) is an invertible coherent module. Serre vanishing
  and the eventual identification of homogeneous coordinates with global sections identify
  that eventual function with the dimension of the degree-m homogeneous coordinate ring.
  Thus this is the numerical polynomial specified in the node, rather than a polynomial
  attached to another ample line bundle. Extension of the residue field to an algebraic
  closure preserves these dimensions, so residue-field fibres encode exactly the geometric
  fibres in the statement. No test field is quantified in an independent universe.
- `∀ P, IsHProjective (HP P).hom ∧ IsSeparated ... ∧ LocallyOfFiniteType ... ∧ QuasiCompact ...`
  gives each stated geometric conclusion. Finite type is the recorded conjunction of
  locally finite type and quasi-compactness, and H-projective is the canonical upstream
  finite-projective-space definition, not a general projective-bundle convention.
- For every P, T and `k : T ⟶ H`, polynomial membership is equivalent to
  `∃! l : T ⟶ HP P, l ≫ ι P = k`. This states representation of the constant-P subfunctor
  by HP, with exactly its inclusion into the full functor. Uniqueness is scheme-theoretic,
  not a condition solely on geometric points.
- `(e.homEquiv (𝟙 H)).1` is the actual universal ideal in E_H. The separate equation for
  every T and k says its ideal pullback is `(e.homEquiv k).1`. It pins the universal
  closed subscheme to the given representing equivalence, rather than choosing an arbitrary
  flat family on H.
- The last conjunct quantifies over every `S' : Scheme.{u}` and every `g : S' ⟶ S`, with
  no Noetherianity assumption on S'. `IsPullback h Hb.hom H.hom g` identifies Hb with H×S S'.
  `eb` represents the full functor for `pullback.snd E.hom g` on every S'-scheme.
- The two equations for a fix both projections of the comparison
  E'×S' Hb → E×S H. These equations uniquely determine the canonical iterated-fibre-product
  map. Equality of `eb.homEquiv (𝟙 Hb)` with the comap of the old universal ideal along a
  states base change as a closed subscheme, including nilpotents. Together with the
  naturality of e and eb this is compatibility of the representing identifications on
  all test maps, not merely existence of some representation after base change.
- For each P, `IsPullback hP HPb.hom (HP P).hom g` identifies HPb with HP×S S'. The equation
  `hP ≫ (ι P).left = ιb.left ≫ h` pins its inclusion into Hb. The final iff with unique
  factorization says it represents precisely the constant-P families after base change.
  The polarization there is pulled back along `pullback.fst E.hom g ≫ i`; its twist is
  exactly the pullback of the original O(m), so the polynomial convention is unchanged.
- There is no flatness instance or hypothesis on E.hom. Every `T : Over S` (and every
  T over S' in the last clause) is arbitrary. The ideal sheaf ⊤ describes the empty family,
  which is allowed throughout. The proof's zero-polynomial observation is retained in
  the docstring; the node's statement does not ask for an additional explicit HP_0 ≅ S.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (every affine open has Noetherian section ring).
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`. Scheme pullbacks and
  the canonical ideal comap are imported through the proper Hilbert presheaf.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`, with its recorded stalkwise equivalence, used by that presheaf.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `LocallyOfFinitePresentation`,
  used by the same presheaf. Its docstring and all-affine-pairs signature were read.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`; finite coordinate type and closed-immersion factorization.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; closed embedding and surjective stalk maps.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` and `IsSeparated`, also used in the existing presheaf.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, and the recorded `QuasiCompact` conjunction.
- `def-pc-representable-functor`: `Mathlib.CategoryTheory.Yoneda`,
  `CategoryTheory.Functor.RepresentableBy`; read both homEquiv and homEquiv_comp.
- Added landed dependency `def-sfb-proper-hilbert-presheaf`:
  `Sheaf.AlgebraicGeometry.ProperHilbertPresheaf`, `properHilbertPresheaf` and
  `IsProperHilbertFamily`. Read the full object, map and functor-law definitions.
- Added definition `def-sfb-projective-fibre-hilbert-polynomial`:
  `Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial`,
  `NumericalHilbertPolynomial` and `HasProjectiveFibreHilbertPolynomial`.
  Its existing building blocks are `ProjectiveSpace.twist` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, the recorded
  `Scheme.Modules.tensorPullback` from `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  and `Scheme.Modules.eulerCharFiber` in
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`. The latter expands into
  the alternating finite sum of residue-field fibre cohomology dimensions, using the
  `Scheme.Modules.eulerChar` convention of `def-pc-euler-characteristic`. The polynomial
  type and evaluation come directly from Mathlib.

The two stated Sheaf proof dependencies are imported privately:
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` and
`Sheaf.AlgebraicGeometry.NoetherianDvrProperness`. The already-matched Mathlib proof tools
are supplied by the public geometric imports and the private FullyFaithful, TorsionFree,
RelativeGluing and Immersion imports. The six geometric Hilbert-construction proof nodes
without Lean records are not replaced or redeclared: flat-graded-tail-Proj, polynomial
locality, free-quotient Grassmannian, graded-tail rank stratum, uniform section bound,
and projective closed-subscheme homogeneous ideal. They are needed only for the future
proof and their argument is retained in the nine-step theorem docstring.

Edge cases checked before stating: n = 0; empty E, S or T; zero polynomial; nonrealizable
or negative numerical polynomials; disconnected T with varying fibre polynomial; nonreduced
and non-Noetherian T; identity base change and arbitrary non-Noetherian S'. When T is empty,
every polynomial membership condition is vacuous, as are its geometric-fibre conditions;
the unique empty-scheme map to every component is exactly what the factorization iff says.
For nonempty T the polynomial is unique by eventual equality of rational polynomials.
No hollow hypotheses, unspecified action, chosen polynomial, or unconstrained comparison
map is introduced. No statement correction or dispute was necessary.

Searches actually run through msearch.py (full responses are in searches.jsonl):

- LeanFinder: full Hilbert representability by projective polynomial components. Eight
  absolute-Proj/properness/affine-space hits, no relative Hilbert representability theorem.
- Loogle: `"Hilbert", "Scheme"`. Zero hits.
- Mathlib grep: `HilbertFunctor|HilbertScheme|hilbertPolynomial`, AlgebraicGeometry. Zero hits.
- LeanSearch: `Hilbert functor flat finitely presented closed subschemes with specified
  fibre Hilbert polynomial`. Eight flatness/finite-presentation/finite-morphism hits,
  no full functor or polynomial predicate.
- Mathlib grep: `IsHilbertFamily|HilbertFamily|NumericalPolynomial|IntegerValued|eulerCharFiber`.
  Zero hits. The separate upstream/project rg found the existing properHilbertPresheaf,
  which was reused, and eulerCharFiber, which is the building block of the new predicate.
- LeanFinder: numerical Hilbert polynomial as eventual fibre-twist Euler characteristic.
  Eight hits on Polynomial.hilbertPoly (a scalar Hilbert-series operation) and absolute
  Proj facts; no numerical-polynomial subtype or projective-family fibre predicate.
- Direct rg of WeilConjectures and Sheaf for Hilbert, HilbertPolynomial, and the proposed
  declaration names; the node-id search in WeilConjectures was empty. Read the fixed-degree
  Hilbert.Defs module and the full ProperHilbertPresheaf module to distinguish them.
- blueprint_refs.py searches for `Hilbert functor`, `numerical polynomial`,
  `fibre Hilbert polynomial`, `fibre Euler`, and grep of DAG definition nodes. The first
  finds three fixed-degree Hilbert nodes, the second three degree/Snapper nodes, and the
  last two none; no node defines the new predicate. The ancestor query returns None,
  as in the current item's blueprint.from.node; this is preserved for the new node.

Primary source read online: [Grothendieck, Expose 221](https://www.numdam.org/article/SB_1960-1961__6__249_0.pdf),
Section 3 (PDF pages 10--18), including the test-base restriction before Theorem 3.1,
Theorems 3.1--3.2, the universal quotient and Hilbert specialization, and Remark 3.9.
The finite-presentation modernization is explicit in the current node and its proof.
Also read [Stacks 0B9T](https://stacks.math.columbia.edu/tag/0B9T), proper finitely presented
flat fibre Euler constancy and arbitrary base change. No archived source was written to
the read-only repository.

## New nodes

`def-sfb-projective-fibre-hilbert-polynomial` defines the numerical-polynomial index type
and the eventual fibre-twist Euler predicate used to cut out the constant-polynomial
subfunctor. It owns `ProjectiveFibreHilbertPolynomial.lean`, with both declarations
recorded in lean.declarations. Its source is the numerical-polynomial formulation in
Grothendieck's Section 3. It has no proofs or choice data. The three required search
kinds and the extra DAG/upstream/project searches above found no existing definition.
The already-landed proper Hilbert presheaf is cited directly instead of being copied.

## Second reading by NX

This is a self-reading; the dispatcher's brief says that the maintainer performs the
independent review and prohibits starting another agent. I reopened the current node,
the full proper Hilbert presheaf, and both delivered modules. The base hypothesis,
over-S compatibility of the closed embedding, coordinate count, all-test-scheme scope,
H-projectivity/separation/finite type, coproduct, fixed-polynomial factorization,
universal ideal and arbitrary-base-change clauses match as detailed above. In particular,
checking only constant-polynomial tests would have lost disconnected-base families;
RepresentableBy for the full presheaf avoids that error. I checked that a is fixed by
both projections and that the base-changed component square commutes with the given
inclusion; otherwise mere abstract representing objects would not assert the canonical
comparison. The new predicate uses the specified twist and the actual tensor pullback,
not a freely chosen invertible module. No substantive mismatch was found. During this
reading I replaced the upstream convenience twistRestrict expression by the recorded
explicit tensorPullback applied to ProjectiveSpace.twist, so the new definition uses
exactly the current module-pullback dependency interface. Both modules are then recompiled.

## Validation

Both modules compile cleanly through scompile.py, separately in dependency order, after
switching to the recorded tensor-pullback interface. The final run reported about 2.1
seconds per file, with no errors or warnings. The definition module has zero sorries;
the main module has exactly the intended theorem sorry. Every Lean line is at most 100
characters; both lean.statement fields are verbatim signatures from their files.

The first dry run rejected the new node's grouped citation brackets: its checker requires
one literal `[id]` per dependency. I separated the four citations into individual brackets;
this changes no mathematical text or dependency. The dry run is repeated after this repair.

The repaired server dry run printed:
`OK (dry run): commit 21fa3b252ad passes the preflight and compiles; nothing pushed`.
The item differs from the current shared node only in lean and stmt_deps. Every new
node dependency is individually cited. The prescribed delivery command follows and
reruns validation with this completed report.
