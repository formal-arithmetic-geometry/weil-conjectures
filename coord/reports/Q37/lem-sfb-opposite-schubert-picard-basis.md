## Worker report

Item: lem-sfb-opposite-schubert-picard-basis. Stage 2: one theorem with `sorry`,
four concrete helper definitions, no proofs completed and no data postponed.
Module: Sheaf.AlgebraicGeometry.GroupScheme.OppositeSchubertPicardBasis.
Main declaration: AlgebraicGeometry.opposite_schubert_picard_basis.

The node statement is unchanged. The helpers belong to the constructions explicitly
introduced by this node, rather than introducing independent mathematical notions:
`schubertBorelOrbit` constructs b ↦ bnB; `schubertOppositeOrbit` constructs
b ↦ (n₀bn₀⁻¹)nB; `schubertReducedClosure` applies Mathlib's vanishing ideal to the
closure of the underlying scheme-map image; `schubertRestrictionDegree` applies the
recorded `Scheme.Modules.degree` to the pullback along the canonical closed immersion.
The last definition explicitly installs the structural morphism to Spec F as the
composite through Q. All four definitions contain real data.

Hypothesis and clause correspondence:

- F algebraically closed: `{F : Type u} [Field F] [IsAlgClosed F]`. There is no
  characteristic assumption.
- G a group scheme: `G : Grp (Over (Spec (.of F)))`, the recorded bundled group-object
  interface. Smooth, connected, affine, finite type, and no smooth connected solvable
  normal subgroup: `hG : IsSemisimpleGroupScheme G.X`. Its definition uses the actual
  scheme-theoretic commutator derived series, not pointwise abstract solvability.
- Simply connected: `hsc` quantifies over semisimple group schemes G', homomorphisms f,
  surjectivity, finite scheme-theoretic kernel and commutation with every algebra
  point. Its conclusion `IsIso f` is exactly the stated central-isogeny condition,
  including nonreduced test algebras and infinitesimal kernels.
- Fixed split maximal torus and Borel: `T B`, `iT iB j`, `hT`, `hsplit`, `hB`, `hj`.
  These are exactly the existing Borel-pair interface and its factorization T → B → G.
- Actual character/cocharacter lattices and positive root system: the two canonical
  commutativity instances, `aG aB haG haB`, `Φ P b hroot hpair hweights hpositive`
  copy the dependency's parameter interface, without copying any definition.
  `haG` and `haB` pin actions to conjugation; `hroot` pins roots to characters;
  `hpair` pins the pairing to integer powers; `hweights` pins Φ to the nonzero weights
  of Lie(G), and `hpositive` pins the base's positive system to the weights of Lie(B).
  The projection p from the dependency is not needed in any assertion here.
- Q=G/B: `Q π hπflat hπsurj hπinv hπtorsor` are the exact right-B-torsor quotient
  interface from the Borel/Bruhat nodes. Q is fixed as an input quotient, so the result
  applies to every such presentation, not merely to some newly chosen scheme.
- W=N_G(T)(F)/T(F): `RankOneRoots.Weyl iT`. `act hact` pin the action to conjugation
  on all test schemes, following the Bruhat theorem. `n hn` choose genuine normalizer
  representatives for every element of this actual quotient.
- Simple roots α₁,...,α_r: the finite subtype `b.support`, which is canonically the
  simple-root set. Enumerating it gives the node's indexing by 1,...,r, with no change
  in strength. `s hs` give its Weyl reflections by precisely the character formula
  x ↦ x − <x,α∨>α, written multiplicatively as division by a character power.
- Longest element: `w₀ hw₀` say exactly that its character action sends the positive
  roots onto their negatives, the characterization supplied by the Bruhat node.
- R_j=closure(B n_sj B/B)_red: `R hR` identify each ideal with
  `schubertReducedClosure (schubertBorelOrbit iB π (n (s i)).val)`.
- B⁻=n₀Bn₀⁻¹ and E_i=closure(B⁻ n_si B/B)_red: `E hE` use
  `schubertOppositeOrbit` with the actual conjugated B map. There is no arbitrary
  opposite subgroup or arbitrary chosen divisor in the conclusion.
- Each R_j is P¹_F: the first conclusion is `Nonempty` of an isomorphism in
  `Over (Spec (.of F))`, with source the canonical composite from `(R i).subscheme`
  through Q. This is an F-scheme isomorphism, not a bijection of underlying points.
- E_i nonempty, reduced, irreducible: `IsIntegral (E i).subscheme`. Mathlib's
  `IsIntegral` entails nonemptiness, reducedness and irreducibility.
- E_i effective Cartier: `(E i).IsInvertible` is the recorded ideal predicate, whose
  actual definition is local generation by a regular element. It does not merely
  assert the abstract invertibility of an unrelated sheaf.
- D_i=n₀E_i: the existential `τ : Q ≅ Q` is pinned by
  `((toUnit G.X ≫ (n w₀).val) * 𝟙 G.X) ≫ π = π ≫ τ.hom`.
  `D i = ((E i).subschemeι ≫ τ.hom.left).ker` constructs precisely the translated
  closed subscheme as its actual kernel ideal. This uniquely characterized descent
  is not an arbitrary automorphism.
- Distinct supports: `Function.Injective (fun i ↦ (D i).support)`.
- Exactly the boundary components: equality of `Set.range` of the D supports with
  the images, under `Subtype.val`, of `irreducibleComponents` of the complement.
  The complement is of `Set.range (schubertBorelOrbit iB π (n w₀).val).left`, namely
  Bn₀B/B=Un₀B/B. The equality of these descriptions is the given Borel factorization
  and the Bruhat longest-cell statement; no alternative open subset is assumed.
- The union assertion is stated separately as that complement equal to `⋃ i, D_i.support`.
- Pic(Q) under tensor product: the actual `Q.left.Pic` with its upstream `CommGroup`
  structure. `Additive` changes notation only.
- d is a group isomorphism to Z^r: `∃ d : Additive Q.left.Pic ≃+ (b.support → ℤ)`.
  The equality for every invertible module L and every j pins d to the restriction
  degree of its Picard class. This is all classes, since the upstream Picard type is
  the invertible part of the module skeleton. The equivalence is therefore the
  specified map, not just an abstract isomorphism of the two groups.
- O_Q(E_i)=I_Ei dual and degree δ_ij: the final clause is exactly
  `schubertRestrictionDegree Q (R j) (E i).toModulesᵛ = if i = j then 1 else 0`.
  The dual and ideal-to-module constructions are those of the recorded dependency.
- Trivial group: no `Nonempty b.support`, positive-rank or positive-dimension
  assumption. If the simple-root support is empty, its function group is the zero
  group. The asserted additive equivalence says precisely Pic(Q)=0, and every
  indexed assertion is empty. The boundary union is the empty union.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic:
  `IsAlgClosed` (the recorded algebraic-closure node explicitly identifies it).
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`;
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: the scheme specialization,
  subgroup/normality predicates and scheme-theoretic kernel terminology.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  `AlgebraicGeometry.reductive_borel_pair_structure`,
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive` and their public terminology.
- Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts:
  `AlgebraicGeometry.bruhat_longest_cell_charts`; its quotient, Weyl-action,
  representatives and positive-reversal interfaces are reused literally.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections:
  `AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections`; the actual
  `RankOneRoots.Weyl` and `normalizer` from its public RankOneRootInterfaces module,
  and the reflection formula in the theorem's character convention.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible:
  `Scheme.IdealSheafData.IsInvertible`, with its full affine-local signature.
- WeilConjectures.AlgebraicGeometry.EffectiveCartier:
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`;
  `Scheme.IdealSheafData.toModules` and `Scheme.Modules.dual` are the actual ideal
  module and its internal-Hom dual. The main formula uses those objects directly.
- WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar:
  `Scheme.Modules.degree`, explicitly specialized to each curve's canonical F-map.
- WeilConjectures.AlgebraicGeometry.Picard.Group: `Scheme.Pic.ofIsInvertible` and
  `Scheme.Pic.instCommGroup`; WeilConjectures.AlgebraicGeometry.PicardFunctor:
  `Scheme.Pic` as the invertible part of the module skeleton.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace: `ProjectiveLine`.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic:
  `Scheme.IdealSheafData.vanishingIdeal` supplies the reduced scheme structure;
  Mathlib.Topology.Irreducible: `irreducibleComponents` is maximal irreducible subsets.

All recorded statement dependencies are public imports, directly or through the
owning modules for the actually used terminology. Available proof modules are plain
imports: regularity, the divisor dictionary, regular-local UFD factorization,
Riemann--Roch/degree agreement (also exposing Curve), and affine-space Picard triviality.
The three proof-only nodes flag-torus-fixed-geometry,
homogeneous-line-schubert-curve-degree and schubert-closure-cell-geometry have no Lean
record or closed upstream audit in the current DAG, so there is no module to import
for them. They remain referenced in the full seven-step proof docstring.

Edge cases checked before finalizing: empty simple-root support, trivial group,
rank one (R₁=P¹, E₁ one reduced point of degree one), rank greater than one (degree
is taken on the curve after restriction, never on the ambient flag variety),
characteristic two (characters, not their differentials, and the full central
scheme-theoretic kernel), characteristic zero, and nonreduced test algebras.
No statement fault, correction or STATEMENT-DISPUTED flag remains.

Searches, made with the prescribed msearch.py wrapper:

- LeanFinder: "The Picard group of a flag variety is identified with integer degrees
  on simple Schubert curves and opposite Schubert divisors give the dual basis".
  Eight hits, all concerning the commutative-ring Picard group, its relative group,
  module representatives, duals and units. None states the flag theorem.
- Loogle: "CommRing.Pic, Scheme.Modules.degree, RootPairing.Base". Zero hits;
  it reports the project-specific name Scheme.Modules.degree unknown to its Mathlib index.
  Its actual upstream source signature was read and is used above.
- Mathlib grep: "Schubert|schubert|Picard" in AlgebraicGeometry. Three explanatory
  comments in EllipticCurve/Weierstrass; no Schubert or scheme Picard theorem.
- LeanSearch: "Schubert divisors of a flag variety and degrees of line bundles on
  Schubert curves". Eight unrelated hits (Lagrange interpolation, abstract ordered
  flags, multivariate polynomial degree, and elliptic division polynomials).
- Direct rg over lean/WeilConjectures and lean/Sheaf found the existing Picard group,
  degree, semisimplicity, Borel, Weyl and simply-connected-character interfaces,
  which are used; no opposite Schubert Picard basis. The node-id search in
  lean/WeilConjectures found no declaration for this item. Full proposed names were
  also checked in both source trees and dag/lean_names_upstream.json: no collision.
- Reduced-closure searches over Mathlib and both project source trees found
  Mathlib's `IdealSheafData.vanishingIdeal` and its explicit reduced-structure
  docstring. The helper is its direct specialization to this node's orbit maps.

Source verified in the primary author-hosted PDF:
https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf,
PDF pages 72--73 and 79--80 (printed pp.62--63 and 70--71). In particular the
exercise heading includes arbitrary characteristic, including zero, and Exercise
2.2.E(2) gives both the dual degrees and the free Picard generators. This supporting
node has no blueprint unit statement of its own; no unit statement was changed.

Compilation: prescribed scompile.py on the complete delivered module succeeded
both as sandbox and under its library module name, with no errors or unexpected
warnings. Every variable and universe is explicit; autoImplicit is disabled.

## Second reading by Q37

Independent second reading by the maintainer's reviewer (the delivered section was a
worker self-check; this section replaces it). The Lean module and the node record are
unchanged.

Node clauses and their Lean rendering (verdict after each):

1. F algebraically closed, any characteristic: `{F : Type u} [Field F] [IsAlgClosed F]`. Right.
2. G semisimple: `hG : IsSemisimpleGroupScheme G.X` (Semisimple.lean:69: smooth, connected,
   affine, finite type, every smooth connected solvable normal closed subgroup terminal;
   solvable = scheme-theoretic derived series). Right; it is the notion that the cited
   borel-pair node's `semisimpleGroupScheme_isReductive` uses.
3. Simply connected: `hsc` (semisimple G', surjective homomorphism, finite kernel, kernel
   central on all F-algebra points ⇒ `IsIso f`). Same form as the landed
   `simplyConnected_character_lattice` and `RhoSectionModules`; no project definition of
   the notion exists. Right.
4. Split maximal torus T ⊆ B ⊆ G, Borel B: `T B iT iB j hT hsplit hB hj`, verbatim the
   borel-pair interface. Right.
5. X*(T), roots, positive roots, simple roots, coroots: `aG aB haG haB Φ P b hroot hpair
   hweights hpositive`, verbatim the conjuncts of `reductive_borel_pair_structure`. Φ is
   pinned to the nonzero Lie(G) weights, the pairing to composition, the base to the
   positive system of Lie(B); for a semisimple group the roots span X_ℚ, so coroots and
   base are determined. Simple-root index `b.support` (r = its cardinality). Right.
6. Q = G/B: `Q π hπflat hπsurj hπinv hπtorsor`, verbatim the dependency's torsor
   interface (Q is then determined up to unique isomorphism). Right.
7. W = N_G(T)(F)/T(F), action, representatives n_w, w₀: `RankOneRoots.Weyl iT`, `act hact`
   (as in bruhat-longest-cell-charts), `n hn`, `w₀ hw₀` (Φ⁺ ↦ −Φ⁺, which determines w₀).
   Right.
8. s_j = s_{α_j} by x ↦ x − ⟨x,α_j^∨⟩α_j: `s hs`; W acts faithfully on X*(T), so s_j is
   determined. Right.
9. R_j = closure(B n_{s_j} B/B)_red: `schubertBorelOrbit` = (b ↦ b·n)≫π, range = BnB/B;
   `schubertReducedClosure` = Mathlib `vanishingIdeal` of the closure (reduced induced
   structure). Right.
10. B⁻ = n₀Bn₀⁻¹, E_i = closure(B⁻ n_{s_i} B/B)_red: `schubertOppositeOrbit` =
    (b ↦ n₀ b n₀⁻¹ n)≫π. Right.
11. R_j ≅ P¹_F: `Nonempty (Over.mk ((R i).subschemeι ≫ Q.hom) ≅ (ProjectiveLine _).asOver _)`,
    an F-isomorphism. Right.
12. E_i nonempty reduced irreducible effective Cartier: `IsIntegral (E i).subscheme`
    (Mathlib class includes `Nonempty`) ∧ `(E i).IsInvertible` (Invertible.lean:62: locally
    on affines a regular principal ideal = def-nagata-effective-cartier-ideal). Right.
13. D_i = n_{w₀}E_i: τ pinned by `((toUnit ≫ n₀) * 𝟙) ≫ π = π ≫ τ.hom` (unique since π is
    fpqc, hence epi); `D i` = kernel of `(E i).subschemeι ≫ τ.hom.left`, the translated
    closed subscheme. Right.
14. Pairwise distinct supports; supports = irreducible components of Q∖C; union:
    `Function.Injective`, the `Set.range = Subtype.val '' irreducibleComponents` equality,
    and the union equality, with C = range of the orbit map at n_{w₀} = Bn₀B/B = Un₀B/B
    (B = U⋊T and n₀Tn₀⁻¹ = T). Right.
15. Pic(Q) and d an isomorphism with d[L] = (deg L|_{R_j})_j: `∃ d : Additive Q.left.Pic ≃+
    (b.support → ℤ)` pinned on every invertible L by `schubertRestrictionDegree`, i.e.
    `Scheme.Modules.degree` (χ(L) − χ(O), def-pc-degree-line-bundle) of the pullback to
    R_j with structure map through Q. Specified map, not an abstract isomorphism. Right.
16. deg(O(E_i)|_{R_j}) = δ_ij with O(E_i) = I_{E_i}^∨: `(E i).toModulesᵛ`, the recorded
    term of def-pc-divisor-line-bundle. Right.

Edge cases: trivial G (b.support empty: Pic(Q) ≃ 0, C = Q, empty union, empty set of
irreducible components of the empty space); rank one; characteristic 2 and 0 (no
characteristic hypothesis, characters not differentials); universes: everything at u,
`A : Type u` test algebras as in the dependencies. No extra hypothesis beyond the node
(the two `IsCommMonObj` instances are true Prop instances copied from the dependency).

Searches: rg "Schubert|schubert" and the helper names over the live lean/ tree: no
Schubert declaration and no name collision. `reducedClosureIdeal` of
def-per-unresolved-strata-geometry is the same one-line Mathlib `vanishingIdeal` wrapper
in another chapter; using Mathlib directly is acceptable (advisory only).

Gates: helpers carry real data and source/blueprint docstrings; the theorem is `by sorry`
with the seven proof steps in its docstring; `lean.statement` is verbatim the file
signature; only the item's `lean` field changed; all imports exist on live.

Mismatches found: none in the Lean or the records. Changed: this section only.
