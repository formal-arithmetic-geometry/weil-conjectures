## Worker report

Item: lem-sfb-central-character-sublattice-quotient. One new module,
`Sheaf.AlgebraicGeometry.GroupScheme.CentralCharacterSublatticeQuotient`, states
`AlgebraicGeometry.central_character_sublattice_quotient`, with one `sorry` and
no definitions or proofs. The node statement, proof and proof dependencies are
unchanged. Three already landed nodes are added to statement dependencies because
the signature uses their diagonalizable-group, character and fppf-quotient interfaces.
No new nodes or dependency repairs are needed.

The source was read in Milne, Algebraic Groups (2017), printed p.461
(Exercise 21-4), and pp.485--486 (Proposition 23.5), from the local PDF.
Exercise 21-4 constructs a reductive central product with the prescribed root datum;
the node is its finite-central-quotient formulation. Proposition 23.5 says that
central isogenies preserve roots and integral coroot pairings. The item is a
supporting node, not the statement of the blueprint unit. The current blueprint
is `literature/blueprint/latest`; no earlier snapshot was used.

Hypothesis-by-hypothesis correspondence:

* `F : Type u`, `[Field F]`, `[IsAlgClosed F]` are the algebraically closed base field.
* `H T : Grp (Over (Spec (.of F)))`, `iT : T ⟶ H`, and
  `hH : IsSemisimpleGroupScheme H.X` are the actual group schemes and torus
  inclusion. The semisimple predicate explicitly includes smoothness,
  connectedness, affineness, finite type and the absence of nontrivial smooth
  connected solvable normal closed subgroup schemes.
* `hT : ReductiveTorusCentralizer.IsMaximalTorus iT` states closed torus inclusion
  and maximality; `hsplit` states the supplied torus is split. No Borel subgroup
  is added to the input.
* `Additive (Character T)` is exactly X_H, the actual group-scheme Hom group,
  with pointwise multiplication written additively. `Φ` is its finite root set.
  The explicit commutativity witnesses supply the usual abelian Hom groups.
* `aH`, `haH` specify conjugation restricted to T. `P`, `hroot`, `hpair` and
  `hweights` express exactly the Borel-pair dependency's convention: roots are
  the nonzero character weights on Lie(H), coroots are actual cocharacters, and
  the integer pairing is composition with the integer power map on G_m.
  These are data/conventions for the root datum in the node, not an additional
  restriction on H. There is no characteristic or separability hypothesis.
* `C : Type u`, `[AddCommGroup C]`, `[Module.Free ℤ C]`,
  `[Module.Finite ℤ C]` are a free abelian group of finite rank.
* The two-factor product `Additive (Character T) × C` is X_H ⊕ C.
  For two factors the product and direct sum coincide. `N : AddSubgroup ...`
  and `[N.FiniteIndex]` are the finite-index subgroup. `hN` is precisely
  `(α,0) ∈ N` for each root α.

Conclusion-by-conclusion correspondence:

* A is `H ⊗ diagonalizableGroup F C`, T_A is
  `T ⊗ diagonalizableGroup F C`. The tensor on group objects over Spec F is
  their fibre product, and `iT ⊗ₘ 𝟙 _` is the actual product inclusion.
* `θ` is T_A ≅ D_F(X). Its first conjunct specifies, for every χ and c,
  the pullback of e^(χ,c) as χ on the T projection times e^c on the other
  projection. Thus θ is the canonical character splitting, not an arbitrary
  isomorphism or an unconstrained map. Global sections are compared with
  `Scheme.ΓSpecIso`, and the Laurent coordinate of G_m is `LaurentPolynomial.T 1`.
* K is literally `diagonalizableGroup F (X ⧸ N)`. `kT` is pinned by
  `kT = diagonalizableGroupMap F (QuotientAddGroup.mk' N) ≫ θ.inv`.
  This is the contravariant Hopf-spectrum map on the prescribed quotient of
  character groups. It retains the group-algebra comultiplication, counit and
  antipode, including their nonreduced spectra.
* `IsClosedImmersion kT.hom.hom.left` asserts the closed subgroup inclusion.
  Since kT is a morphism of bundled group objects, compatibility with the group
  structure is already in its type. `IsFinite K.X.hom` states finiteness;
  for the displayed affine group-algebra spectrum this is equivalently finite
  dimensionality of F[X/N]. It does not mean finiteness of geometric points.
* The universal R, CommRing R, Algebra F R, k, g clause expresses centrality
  on every commutative F-algebra, including nonreduced ones. The explicit
  `@Commute` fixes the Hom group of the product scheme; it avoids an instance
  inference failure on the reducible bundled product, with no mathematical
  restriction or auxiliary assumption.
* G and q are existential actual group schemes and their quotient map.
  `IsFppfGroupQuotient (kT ≫ (iT ⊗ₘ 𝟙 _)) q` supplies the scheme-theoretic
  kernel square, the canonical right-multiplication torsor, local surjectivity,
  sheafness and the sheafification universal arrow from the coset coequalizer.
  This is the represented fppf quotient in the node, rather than a quotient of
  F-points or an arbitrary map. Restricting the scheme fppf topology to affine
  test objects gives the faithfully flat finitely presented algebra coverings
  in the node.
* `Flat q.hom.hom.left ∧ Surjective q.hom.hom.left` states faithful flatness.
  `Smooth G.X.hom`, `ConnectedSpace G.X.left`, `IsAffine G.X.left`,
  `LocallyOfFiniteType G.X.hom` and `QuasiCompact G.X.hom` are exactly the
  stated smooth connected affine finite-type geometry. The recorded
  `ReductiveTorusCentralizer.IsReductive G` is reductivity with no nontrivial
  smooth connected normal unipotent subgroup, after algebraic closure.
* `iS : S ⟶ G`, its maximal-torus predicate and its split-torus isomorphism
  make S a split maximal torus. The equality of composites identifies q on T_A
  with qT followed by iS; `IsFppfGroupQuotient kT qT` states S = T_A/K.
  Thus S is the sheaf-theoretic image, without asserting surjectivity on points
  over every test algebra.
* `e : Additive (Character S) ≃+ N` is the character-lattice identification.
  Its coordinate equality specifies actual pullback along qT: χ pulls back
  to the group-algebra character e^(e χ), via θ. Hence its inclusion into X
  is exactly qT*, injective with image N.
* `aG` is pinned to restricted conjugation by iS. `Q` is the root datum on
  the actual character and cocharacter groups of S. The nonzero weight-space
  equivalence says these, and only these, are its roots. The equation
  `(e (Q.root α)).val = (α.val,0)` identifies every root with (α,0) in N.
* The power-map equation pins Q's pairing to genuine character/cocharacter
  composition. The last equality is exactly
  `c^N_α(n) = c_α(pr_X_H n)`: write n = e χ, and use
  `Q.toLinearMap χ (Q.coroot α) = P.toLinearMap (e χ).val.1 (P.coroot α)`.
  Since e is onto N, this covers every n. The isomorphism to the dual lattice
  is the perfect pairing already part of RootDatum, so coroots are integral
  Hom(N,ℤ) functionals, not differentials.

Dependency declarations read and used:

* Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, and `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, as specified by the two field nodes.
* `CategoryTheory.GrpObj`, `Grp`, `IsMonHom` and the Hom group structure in
  `Mathlib.CategoryTheory.Monoidal.Grp`; specialization and finiteness/kernel
  conventions in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
* `AlgebraicGeometry.reductive_borel_pair_structure` and
  `semisimpleGroupScheme_isReductive` in
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`, including
  the full docstrings, actual Hom groups, power-map pairing and tangent weights.
* `IsSemisimpleGroupScheme` in `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`;
  `IsMaximalTorus`, `IsReductive` in
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`; `splitTorus`
  in `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`.
* Already landed `def-sfb-diagonalizable-group` supplies `diagonalizableGroup`
  and `diagonalizableGroupMap` from `Sheaf.AlgebraicGeometry.DiagonalizableGroup`.
  They use actual `hopfSpec` and `AddMonoidAlgebra.mapDomainBialgHom` data.
* Already landed `def-sfb-rank-one-root-interfaces` supplies `RankOneRoots.Character`
  and `RankOneRoots.Cocharacter` from
  `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`. These abbreviate
  exactly the dependency's Hom groups; they introduce no private lattice copy.
* Already landed definition node `def-sfb-fppf-group-quotient-presentation` owns
  `IsFppfGroupQuotient` from
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`.
  Its complete definition and docstring were read.
* The stated proof dependencies are imported without `public`: affine flat image,
  multiplicative character antiduality, the rational-point geometric-connectedness
  criterion, Mathlib smooth composition and Mathlib connected components for
  geometrically connected maps. The remaining proof dependency nodes have no
  recorded Lean declaration yet, so no module can be imported for them. Their
  complete eight-step route is retained in the theorem docstring.

Edge cases checked before finalizing:

* H = 1: T and X_H are trivial, Φ is empty, and the construction is the
  finite diagonalizable quotient of D(C). No nonempty root index is assumed.
* C = 0: a zero-rank free module is permitted and D(C) is the trivial group.
* N = X: X/N is zero and K is trivial; q may be an isomorphism and S = T_A.
* H = 1, C = 0: both source and quotient are trivial, with empty root datum.
* In characteristic p, H = 1, C = ℤ and N = pℤ give K = μ_p.
  No Smooth or Etale hypothesis is placed on K or q. The kernel and all
  centrality tests retain nonreduced algebras. Thus inseparability is included.
* The product Hom class failure was repaired by specifying the ordinary
  tensor-product Hom type for Commute, not by assuming another structure.

Searches made (the prescribed msearch wrapper records full raw responses in
`searches.jsonl`):

* LeanFinder: “Finite central diagonalizable quotient of semisimple group times
  split torus has prescribed character sublattice and restricted coroots”:
  8 unrelated root-pairing/Geck/Lie-algebra hits, no group-scheme quotient theorem.
* Loogle: `"GroupScheme", "quotient"`: 0 hits.
* Mathlib grep: `central.*quotient|quotient.*reductive|character.*sublattice`
  in AlgebraicGeometry: 0 hits.
* LeanSearch: “finite central quotient algebraic group character lattice roots
  coroots”: 8 abstract root-system or Lie-algebra hits, no match.
* rg on both `lean/WeilConjectures` and `lean/Sheaf` with the same pattern and
  the item id: only unrelated central-radical Lie results and the adjoint-kernel
  central-unipotent quotient. No existing declaration states this node.
* Further source rg located the existing diagonalizableGroup/Map, Character,
  Cocharacter, semisimple, maximal-torus, tangent-weight and fppf-quotient
  declarations, all reused. DAG records were checked for their owning nodes.

No statement correction or disputed mathematical claim is reported. Compiles use
only scompile.py, against the published live build. The first clean compile took
4.8 seconds in the sandbox and 2.7 seconds under the library module name.

## Second reading by NX

This is a separate self-review pass, not a claim of review by another agent;
the dispatcher forbids starting other agents and the maintainer supplies the
independent review. I reread the node and full signature together. In particular,
θ is normalized on every e^(χ,c); the kernel inclusion is fixed by its equation;
centrality quantifies over rings rather than only fields; both fppf presentations
retain their scheme-theoretic kernel; e is fixed by qT pullback; roots are exactly
nonzero tangent weights; and the coroot equality quantifies over every χ, hence
over every n in N. No input Borel, characteristic restriction, smooth kernel or
separability of q was introduced. The finite-index condition and zero-rank cases
were retained. No mathematical mismatch was found in this pass. The only earlier
repairs were a mistaken Mathlib import path and product-Hom instance elaboration.

## Returned delivery repair (H2)

The returned immutable head was 4e3b06c116b6. Its only requested repair
was the DAG owner of `AlgebraicGeometry.IsFppfGroupQuotient`. I read the
current live definition node `def-sfb-fppf-group-quotient-presentation` (Q95),
whose existing Lean record points to exactly the definition at
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry:60`.
Its statement covers the kernel square, local surjectivity, represented sheaf,
torsor projections and coset-sheafification universal property used here.

Replaced `lem-sfb-affine-normal-quotient-geometry` in `stmt_deps` by
`def-sfb-fppf-group-quotient-presentation`. The quotient-geometry theorem remains
in `proof_deps`, where the proof uses its existence and geometry conclusions.
The module, imports, Lean signature, natural-language statement, proof and
proof dependencies are unchanged from the returned delivery. All other node
fields are taken from the current live base; the prescribed delivery wrapper
rebases the repaired packet onto current main. The optional extra dependency
citations were not needed for this repair.

Rechecked that the node's Lean statement is verbatim from the unchanged file.
The maintainer's independent mathematical review of the returned head accepted
all hypotheses and conclusions, including zero ranks and nonreduced kernels;
this metadata correction does not alter those checks.
