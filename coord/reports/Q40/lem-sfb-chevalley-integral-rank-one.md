## Worker report

Module: `Sheaf.AlgebraicGeometry.GroupScheme.ChevalleyIntegralRankOne`.
Main declaration: `AlgebraicGeometry.ChevalleyIntegralRankOne.integral_rank_one`.
This is a statement delivery: its single theorem has proof `sorry`; the five helper
constructions contain actual data. There is no correction to the natural-language node.

Read the item, all its statement dependencies and recorded declarations, the full
Chevalley-admissible-representation module, root-datum-lattice-embedding module,
reductive-Borel-pair module, group-scheme/subgroup definitions and standard group
schemes. Read Milne, Algebraic Groups (2017), printed pp.508--511, especially
admissibility, (152), (153), Theorem 23.72's omitted rank-one details and Corollary 23.73.
Read the latest blueprint's `det-thm-sf-ctf-stability-direct-images` statement and proof
(3); this supporting node has no blueprint-unit identity of its own.

Hypothesis and clause correspondence:

- `V`, its module and finite-dimensional instances, `R`, `c`, `hfinite`, `hne`,
  `hspan`, `htwo`, `hint`, `hreflect`, `hreduced` express the spanning reduced
  crystallographic rational root system with the same explicit axioms as the
  Chevalley-representation dependency. `P` and `hP` express exactly the integer-valued
  weight lattice. `rootWeight` with `hrootWeight` names the canonical root inclusion;
  `neg` with `hneg` names the unique negative root. These do not restrict the root
  system: integrality puts every root in P, and a root reflection sends a to -a.
- `g` with its Lie and finite-dimensional instances and `hsemisimple` is the split
  semisimple rational algebra. `H`, `hab`, `hmax` give the maximal abelian Cartan;
  `θ` identifies H with the rational dual of V. `he` and `hdecomp` give the nonzero
  root eigenvectors and Cartan/root direct sum, hence simultaneous diagonalization.
  This uses precisely the same objects and weight-space construction as the recorded
  dependency, not a second Lie-algebra or weight-space definition.
- `r`, `b`, `hb`, `hbase` give the fixed simple-root base: a rational basis made of
  roots, and every root has integer coordinates either all nonnegative or all
  nonpositive. `B`, `hBsimple`, `hBroot` give the Chevalley basis in that base;
  `hopposite`, `hbracket`, `hzero` spell out all the opposite-root, root-string and
  zero-bracket conditions of the Chevalley dependency. The finite base may be empty.
- `W` and its Lie-module instances, finite dimension and `LieModule.IsFaithful` are
  the faithful representation. `Λ`, `hlattice`, `Module.Free` give the full lattice.
  `Ω`, `hweights` give exactly the nonzero weight spaces with integral weights;
  `hW` is their rational direct sum, `hΩ` is ZΩ=P, and `hΛ` is the internal direct
  sum of their intersections inside Λ. `hnil` is root-operator nilpotence and
  `hdiv` is stability under every rational divided power, including m=0.
- `I`, its finite-index instances and `bΛ : Module.Basis I ℤ Λ` are arbitrary
  coordinates on the actual lattice, as in Milne's paragraph before (153). Such
  coordinates always exist for a full finite-rank free lattice. Scalar extension
  sends them to a basis of Λ tensor F, so `GeneralLinearGroup I F` is exactly GL(W_F)
  in these coordinates. No representation or lattice is replaced by an unrelated one.
- `F`, `Field F`, `IsAlgClosed F` give the algebraically closed field, with no
  characteristic restriction. `diagonalizableGroup F P` is exactly Spec F[P] with
  its existing Hopf structure. `iT` is its closed weight embedding, with
  `IsClosedSubgroupScheme iT.hom.hom` and the displayed `mulVec` eigenvalue identity
  on every integral weight vector, after arbitrary algebra extension. Those vectors
  span every extended weight summand by `hΛ`.
- `χ` is the actual family of weight characters. Its Laurent-coordinate equality
  with `weightValue t lam` pins it to the group-algebra basis element e^lam on
  every algebra point. The condition on `h a ≫ χ lam` pins h_a to the integral
  exponent c_a(lam), using integer powers of the identity morphism of G_m.
- `dividedPowerMatrix` restricts `(m!)⁻¹ E^m` to Λ using the supplied admissibility
  proof, then takes its matrix in bΛ. `exponentialMatrix` sums these integral
  matrices up to `nilpotencyClass E`, mapping integer entries into the test algebra.
  Higher terms vanish. The equality for `homMulEquiv ... (rootPoint (x a) z)`
  specifies precisely x_a(z)=sum D_(a,m) z^m; there is no factorial inversion in F.
  The existential x maps are morphisms in the group-scheme category, uniquely pinned
  by these all-algebra matrix identities. `rootPoint` is polynomial substitution
  into the already recorded additive group followed by x, not an arbitrary map.
- Every x_a is closed: `∀ a, IsClosedSubgroupScheme (x a).hom.hom`.
  `∀ a, ∃ v : RankOneRoots.SL2Hom ...` gives the required group-scheme SL2 map as
  its natural family on determinant-one matrices. The three following clauses
  specify upper unipotents, lower unipotents with the SAME parameter/sign, and
  diag(s,s⁻¹), respectively. Quantification over a determinant-one matrix q whose
  entries equal the displayed matrix avoids choosing proof terms for determinant one.
  For every z (or unit s) that determinant-one matrix exists, including over zero rings.
- For each a, `J,j,t,upper,lower` give the generated closed subgroup and the three
  factorizations of T,x_a,x_-a. The universal factorization through every closed K
  containing those three maps is exactly the smallest-closed-subgroup condition.
  `IsReductive J`, `IsMaximalTorus t`, and the split-torus isomorphism clause express
  split reductivity with the specified split maximal torus. `act.smul` is pinned
  to the actual conjugation by t. The `weightSpace` equivalence says its roots are
  exactly the two characters corresponding to ±a, using characters on tangent vectors,
  not differentiated characters. The last clause in this J block identifies the
  coroot as h_a by the character-reflection characterization: any cocharacter
  inducing the actual a-reflection on every character equals h_a. The preceding
  exponent formula for h_a together with the following reflection formula shows
  h_a itself satisfies that characterization (and c_a(a)=2 gives pairing two).
- `∀ i j : Fin r, i ≠ j → ... Commute ...` is precisely commutation of x_-a and
  x_b for distinct simple roots, with independent parameters z,w over every algebra.
- `weylPoint` is x_a(1)x_-a(-1)x_a(1). `reflection a` is a torus automorphism;
  its all-algebra conjugation identity is normalization of T. The subsequent
  equality with `χ κ` pins its pullback on every character to lam-c_a(lam)*a.
  Such κ exists in P, since the root and the pairing are integral.
- `∃ ε : R → R → ℤ` with signs ±1 supplies fixed signs for all root pairs,
  independent of test algebra or parameter. The reflected-root equality and the
  conjugation formula give exactly n_a x_b(z) n_a⁻¹=x_(s_a b)(ε_(a,b)z).
- For each gamma, `δ : Fin r`, `word : List (Fin r × ℤ)`, its exponent condition,
  and a fixed sign give a finite word in the simple n_a and their inverses.
  The final displayed identity is the required conjugation of x_delta to x_gamma.
  The empty word is allowed; no root is assumed simple or positive.

Dependency declarations actually reused:

- `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding`: `RootDatumLattice.lattice_embedding`
  provides the explicit rational-root/weight-lattice conventions, used inline on V
  exactly as by its Chevalley-representation consumer.
- `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation`:
  `LieAlgebra.exists_chevalley_admissible_representation`; its existential output
  is expanded into this theorem's given-data binders without a private predicate.
- Mathlib `Field`, `IsAlgClosed`, `CategoryTheory.Grp`, `GrpObj`, `IsMonHom` are
  the recorded field, algebraic-closure and group-scheme notions.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme` and its underlying `IsSubgroupScheme`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `additive`,
  `multiplicative`, and their recorded group structures.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure` and its public
  terminology imports: `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`,
  `MultiplicativeType.splitTorus`, `TorusCharacterTangent.weightSpace`.
- Landed definition node `def-sfb-diagonalizable-group`, module
  `Sheaf.AlgebraicGeometry.DiagonalizableGroup`, declaration `diagonalizableGroup`.
- Landed definition node `def-sfb-rank-one-root-interfaces`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`, declarations
  `RankOneRoots.SL2Hom` and `RankOneRoots.multiplicativeValue`.
  These two existing nodes are added to stmt_deps under the landed-node addition
  rule of brief-stage2 section 5. No new node or dependency repair is needed.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `GeneralLinearGroup`, its canonical group structure and `homMulEquiv`.
- Mathlib `LinearMap.restrict`, `LinearMap.toMatrix`, `nilpotencyClass`, and
  `Matrix.SpecialLinearGroup` provide actual linear/matrix constructions.

Already recorded proof dependencies are imported privately: character antiduality,
rank-one reflections, affine-homomorphism flat image, and root-base Mathlib results.
The admissible representation is public because the statement uses its objects.
Other proof dependencies currently have no recorded module and supply no import;
the entire twelve-step proof plan is preserved in the theorem docstring.

Edge cases checked before and during the clause audit:

1. R empty implies V=0 and P=0. Root-indexed conclusions are vacuous, while the
   trivial weight torus still acts identically. Its coordinate/weight-action clause
   is intentionally NOT indexed by a root. The simple base has r=0 and no simple
   pair or final gamma instance is required.
2. Rank-one A1: the standard two-dimensional representation gives the displayed
   upper/lower SL2 matrices, torus diag(s,s⁻¹), n=[[0,1],[-1,0]], reflection of
   weights and the negative-root sign; adjoining a trivial weight summand causes no issue.
3. Zero weight, multiple weight-space dimension, and arbitrary lattice coordinates:
   the action condition is tested on all vectors in the actual intersection, rather
   than an assumed weight-compatible basis. No weight multiplicity one is imposed.
4. The zero-dimensional vector-space convention causes `nilpotencyClass` to be zero;
   the empty exponential sum is the unique empty matrix, also the identity. Nonempty
   roots and faithfulness in fact preclude this case, but helpers remain well typed.
5. Characteristics 2 and 3: signs and exponentials reduce from integers; m! is only
   inverted over Q before lattice restriction. Opposite signs may coincide in char 2,
   which the formulas allow. No differentiated-weight separation is assumed over F.
6. Nonreduced algebras (e.g. F[epsilon]/epsilon²), arbitrary zero divisors, and the zero
   algebra are included by `A : CommAlgCat F`; the SL2 family is natural for every
   algebra map, and every point identity quantifies over those A.
7. The word may be empty, and negative exponents are restricted to -1; the sign is
   chosen outside all test-algebra quantifiers. No pointwise choice can change it.

Searches actually performed, 2026-10-24:

- msearch LeanFinder: "Integral Chevalley representation root subgroups SL2 Weyl
  reflection normalizes weight torus". Eight hits: abstract root-pairing Weyl-group
  results, Geck construction, and Lie sl2 subalgebra; no matching integral group-scheme result.
- msearch Loogle: "Matrix.SpecialLinearGroup, LieModule.weightSpace,
  AlgebraicGeometry.GeneralLinearGroup". Zero hits; the service reports the last
  identifier unknown (it is a project declaration). This is not treated as an
  exhaustive absence result.
- msearch LeanSearch: "Chevalley root subgroup integral lattice SL2 Weyl action".
  Eight hits, all abstract root-pairing/Weyl-group results except a modular-forms
  strict-period subgroup; none states the node.
- msearch Mathlib grep: `chevalley|Chevalley|SL2Hom`. Twenty-five hits, mainly
  Jordan--Chevalley, Chevalley--Warning, Beck--Chevalley, and Lie bases; no match.
- rg in `lean/WeilConjectures` for `chevalley|Chevalley` and the exact item id:
  Chevalley constructibility results and unrelated Beck--Chevalley maps; no item.
- rg in `lean/Sheaf` for Chevalley/rank-one/SL2/diagonalizable names found the
  admissible representation, integral root model (different statement), rank-one
  root interfaces and existing group-algebra construction. Those were read and reused.
- rg of `dag/lean_names_upstream.json`, `WeilConjectures`, `Sheaf` for the new
  namespace and declaration/helper names found no pre-existing declaration.
- Read the two existing extra definition nodes in full. A read-only graph traversal
  found no dependency path from either of them to this item; no dependency cycle is added.

Validation: scompile.py compiled both the sandbox probe and the actual module with
no errors and no warnings (28.8s and 14.4s respectively). All variables/universes are
explicit, all lines are at most 100 characters, and the lean.statement is extracted
verbatim from the declaration signature. Dry-run and final delivery results follow
from the required delivery wrapper.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
