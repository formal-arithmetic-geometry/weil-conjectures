## Worker report

The module `Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure` states
`AlgebraicGeometry.CocharacterLimit.smooth_connected_structure`, with its sole proof
postponed by `sorry`. Four real-data helper definitions in the same module render the
limit conditions already defined in this node: `IsOrbitExtension`, `parabolicPoints`,
`unipotentPoints`, and `centralizerPoints`. No group, map, action, character, or vector
space is defined by an unconstrained choice or `sorry`.

Sources read: Milne, Algebraic Groups (2017), printed pp.261--266 (PDF pp.273--278),
Definition 13.21, Propositions 13.23--13.24, 13.28--13.30, Theorem 13.33 and its proof;
printed p.283 (PDF p.295), Corollary 14.12 and Example 14.13. The current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read: this item is a supporting algebraic-group assertion, not that unit's own
six-functor statement. The compact-object example requested in the brief is now a
withdrawn module with no declarations; the delivered header follows the current module
mode conventions and the extant GmRepresentationWeightBasis example instead.

Hypothesis and clause correspondence:

- The algebraically closed field F is `{k : Type u} [Field k] [IsAlgClosed k]`.
  The group scheme is `G : Grp (Over (Spec (.of k)))`. Affineness is
  `[IsAffine G.X.left]`; finite type is `[LocallyOfFiniteType G.X.hom]` and
  `[QuasiCompact G.X.hom]`; smoothness is `[Smooth G.X.hom]`; connectedness,
  including nonemptiness, is `[ConnectedSpace G.X.left]`. No characteristic
  restriction or reductivity hypothesis is imposed.
- The cocharacter is the actual group-scheme homomorphism
  `lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G`, with the recorded
  Laurent Hopf group law. Multiplicative-group points are actual scheme points,
  equivalently units; the universal Laurent coordinate is not replaced by testing
  only the ground field's units.
- For each commutative test algebra `A : CommAlgCat.{u} k`, `IsOrbitExtension lam A g q`
  says the morphism `q : Spec A ⊗ G_a ⟶ G` restricts to
  `lam(t) * g * lam(t)⁻¹` on `Spec A ⊗ G_m`. The restriction is tensoring the identity
  with `StandardGroupSchemes.map k Polynomial.toLaurentAlg`, the actual inclusion
  of G_m in the affine line. By the product universal property, a k-morphism from
  this product to G gives exactly an A-morphism to G_A. Thus the encoding retains
  the relative morphism required in the node, with no arbitrary base map.
- `parabolicPoints` is existence of this extension. `unipotentPoints` requires in
  addition `lift (𝟙 _) 1 ≫ q = 1`; the first `1` is the additive group's identity
  section, namely coordinate zero, and the second is the identity point of G.
- `centralizerPoints` requires commutation with `s ≫ lam.hom.hom` for every algebra
  `B`, every map `f : A ⟶ B` and every B-point `s` of G_m. The point `g` is extended
  by the actual `StandardGroupSchemes.map k f.hom`, so nilpotents are retained.
- The existential `P U Z` and their group homomorphisms `iP iU iZ` have the three
  `IsClosedSubgroupScheme` conclusions, and each has its own `Smooth` and
  `ConnectedSpace` conclusion. Three universally quantified biconditionals identify
  their point images with precisely the three sets above. Closed subgroup schemes
  of finite-type affine G are automatically affine and finite type, so those
  inherited properties do not add a separate assumption.
- The existential homomorphism `j : U ⟶ P` satisfies `j ≫ iP = iU` and
  `IsNormalSubgroupScheme j.hom.hom`. Normality is thus in P, as the node requires.
- The scheme isomorphism `e : U.X ⊗ Z.X ≅ P.X` has
  `e.hom ≫ iP.hom.hom = (fst ≫ iU.hom.hom) * (snd ≫ iZ.hom.hom)`, so it is
  the multiplication map. The morphism `c : Z.X ⊗ U.X ⟶ U.X` is pinned by
  `c ≫ iU = iZ(z) iU(u) iZ(z)⁻¹`. The final universally quantified formula for `e`
  states exactly `(u,z)(u',z') = (u * c(z,u'), z*z')`. This specifies the
  semidirect group scheme on the required product scheme and says multiplication
  is a group-scheme isomorphism, without identifying the semidirect group law
  with the ordinary direct-product group law.
- `SolvableGroupStructure.IsUnipotent U` is the already-landed definition: U is
  smooth and there is a closed-immersion representation into finite matrices,
  with `(u-I)^N = 0`, `0 < N`, for every geometric point. Its smoothness conjunct
  is already part of this node's conclusion. The definition uses finite matrix
  size, not a single unconstrained homomorphism of geometric groups.
- The action `a : ModObj G_m G` is fixed by the equality
  `a.smul = (fst ≫ lam) * snd * (fst ≫ lam)⁻¹`; it is exactly conjugation.
  For every `n : ℤ`, `(chi n).hom.hom = (𝟙 G_m)^n` fixes the actual character
  t ↦ t^n. `W n` is equal to the existing
  `@TorusCharacterTangent.weightSpace ... a (chi n)`. That definition uses the
  action on actual dual-number tangent points at the identity. Over algebraically
  closed k, rational points of the split torus are dense, so its character test
  is the same integer-character weight space, in every characteristic.
- `DirectSum.IsInternal W` is the stated internal direct sum of Lie(G).
  The three final equalities identify the ranges of the differentials of `iZ`,
  `iU`, and `iP` with `W 0`, `⨆ n > 0, W n`, and `⨆ n ≥ 0, W n`, respectively.
  These are submodules of the one canonical `GrpObj.Lie G.X`; directness of W
  makes each displayed supremum the subspace underlying the required direct sum.
  This retains tangent images, rather than comparing dimensions or abstractly
  isomorphic Lie algebras.

Dependency interfaces read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic:
  `IsAlgClosed` (the algebraic-closure node's recorded match explicitly names it).
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, `Grp`, group homomorphisms;
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` and their full test-algebra signatures.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`;
  Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`;
  Mathlib.Topology.Connected.Basic: `ConnectedSpace`.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `affine`, `map`, `multiplicative`,
  `multiplicativeGroup`, `additive`, with the actual zero identity section.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic/Ring/Bracket/Differential:
  `GrpObj.Lie`, `tangentPoint`, `lieEquivTangent`, `differential`.
- Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights:
  `TorusCharacterTangent.weightSpace`; Sheaf.AlgebraicGeometry.SolvableGroupStructure:
  `SolvableGroupStructure.IsUnipotent`. Their already-landed owning nodes
  `def-sfb-torus-character-tangent-weights` and `def-sfb-solvable-group-structure`
  were added to stmt_deps, as authorized for landed definitions. No node statement
  or proof was corrected.
- Plain proof imports retain the stated proof dependencies:
  Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis,
  Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth,
  Sheaf.AlgebraicGeometry.TransverseSubgroupProductOpen, and
  WeilConjectures.AlgebraicGeometry.Regular (`IsRegular.of_smooth`,
  `IsRegular.isIntegral`). Their signatures and docstrings were read. The faithful
  embedding and smooth concentrator nodes have no Lean record yet, so there is
  currently no module of either to import; neither notion occurs as a missing
  prerequisite in this theorem's type. The complete seven-step proof remains in
  the theorem docstring.

Edge cases checked before drafting: trivial G and zero Lie algebra; trivial or central
cocharacter (P=Z=G and U=1, weight zero only); positive and negative weights in the
SL2 example; repeated weights in GL3 (block diagonal centralizer); positive
characteristic (characters are not replaced by their differentials modulo p);
A=0 (empty test scheme, unique points); nonreduced A, including dual numbers;
identity algebra map and arbitrary noninjective algebra maps in the centralizer
condition; negative exponents on units. The test algebras share the scheme/field
universe u; no smaller independent universe can make a quantifier vacuous.
The ambient group cannot be empty because it has an identity; ConnectedSpace also
requires nonemptiness. The full direct sum includes all integers, not just weights
which happen to be nonzero.

Searches for an existing statement (outputs retained in searches.jsonl by msearch):

- leanfinder: `Smooth connected cocharacter limit subgroups semidirect product positive
  tangent weight spaces`: eight abstract Lie-module/weight-space hits, no affine
  group-scheme limit-subgroup statement.
- loogle: `GrpObj, IsClosedSubgroupScheme`: no hits; GrpObj unrecognized by the
  remote index. Local source searches supply these known dependency interfaces.
- leansearch: `Cocharacter attracting subgroup smooth connected unipotent Lie algebra
  positive weights`: eight Lie-module or root-space hits, no matching statement.
- msearch grep: `cocharacter|Cocharacter|IsUnipotent`, Mathlib AlgebraicGeometry:
  no hits. Local rg over WeilConjectures and Sheaf for cocharacter, tangent, adjoint,
  unipotence and semidirect products found the reused weight/unipotence notions and
  the distinct conjugation-into-a-torus theorem; no theorem with this conclusion.
  Exact item-ID search in WeilConjectures found no declaration. Source searches
  also found the canonical Lie differential, so no second tangent/Lie interface
  was introduced. No new definition node or dependency repair is needed.

Validation: scompile.py compiled the module both as a sandbox file and at its library
module path, with no error or non-sorry warning. An initial incorrect DirectSum import
path was repaired to Mathlib.Algebra.DirectSum.Internal. All compiles used scompile.py;
no source checkout or live library file was modified. Dry-run and delivery results
are recorded below after execution.

## Second reading by O3

The dispatcher prohibits starting another agent; this is a second pass by the same
worker, with the node and final Lean file open. The maintainer supplies the independent
review. I rechecked the correspondence above, especially that the zero section uses
the additive identity, the centralizer quantifies over all A-algebras rather than
only field-valued points, normality is in P, and the multiplication on U times Z is
the conjugation semidirect law. I checked that the action and characters are fixed by
morphism equalities, and that the Lie conclusions concern differential ranges in
Lie(G), with no chosen identification of an unrelated vector space. The initial draft's
placeholder action was replaced with the actual conjugation formula before any clean
compile. The import-path error was repaired; no mathematical hypothesis, clause,
source statement, proof step, or proof dependency changed. No unresolved statement
dispute was found.

The prescribed `deliver2.py O3 lem-sfb-cocharacter-limit-smooth-structure --no-push`
completed successfully: `OK (dry run): commit 43d955a5d9c passes the preflight and
compiles; nothing pushed`. The delivery contains exactly the item node, its module,
and this report.
