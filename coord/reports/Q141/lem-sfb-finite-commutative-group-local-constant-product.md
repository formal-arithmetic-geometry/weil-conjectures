## Worker report

The module Sheaf.AlgebraicGeometry.FiniteCommutativeGroupLocalConstantProduct states
AlgebraicGeometry.finiteCommutativeGroup_localConstantProduct. Its only postponed proof is
that theorem. The three data definitions are transparent constructions: packaging the
recorded constant scheme as an Over object; its recorded coprojection as an Over morphism;
and identity evaluation on the recorded open identity component. They introduce no new
independent notion and make no choice of a group structure or a decomposition map.

The node statement is unchanged, with every clause represented as follows.

- K algebraically closed: `(K : Type u) [Field K] [IsAlgClosed K]`.
- A finite commutative K-group scheme: `G : Over (Spec (.of K))`, `[GrpObj G]`,
  `[IsCommMonObj G]`, `[IsFinite G.hom]`. There are no extra hypotheses on G.
- C is precisely the identity component with the open subscheme structure:
  `GrpObj.identityComponent G`, defined upstream as the open subscheme on
  `connectedComponent (GrpObj.onePoint G)`. The conclusion includes `IsClopen` of this
  very set. Its use requires only locally finite type and quasi-compactness, inferred
  from finiteness of G, rather than added as assumptions. The inherited upstream group
  structure restricts the multiplication, unit and inverse of G through the open inclusion.
- C is finite, connected, commutative and a subgroup: `IsFinite C.hom`,
  `ConnectedSpace C.left`, `IsCommMonObj C`, `IsSubgroupScheme (GrpObj.identityComponentι G)`.
  The upstream `GrpObj C` is the actual restricted group law.
- H = G(K): `(𝟙_ (Over (Spec (.of K))) ⟶ G)` with its existing Hom commutative group.
  `Finite` expresses its finiteness. `Additive` merely changes notation for this same
  group when feeding it into the existing additive constant-group-scheme interface.
- H_K is the coproduct of Spec K indexed by H: `finiteGroupConstantPoints G` packages
  `constantGroupSchemeProjection (Spec (.of K)) (Additive H)`. It is not a new
  construction of a constant scheme. The conclusion provides a `GrpObj` on this precise
  scheme and equates its multiplication, as a Scheme morphism, to the dependency's
  `constantGroupSchemeMultiplication`. It also records commutativity. Thus this is the
  prescribed componentwise group law; the group axioms determine its unit and inverse.
- The displayed isomorphism is `φ : C ⊗ finiteGroupConstantPoints G ≅ G` in Over Spec K,
  with `IsMonHom φ.hom`. Here the cartesian tensor in Over is the scheme fibre product.
  It is an isomorphism of group schemes: an invertible homomorphism has homomorphic inverse.
- The map is the one specified in the node: for EVERY h, precomposing φ.hom with
  `lift (𝟙 C) (toUnit C ≫ finiteGroupConstantPointsIncl G h)` equals
  `GrpObj.identityComponentι G ≫ GrpObj.mulLeft G h.toMul`. The left map includes the
  h-component C = C ×_K Spec K; the right map is its translation in G. Commutativity
  identifies left translation with the node's additive translation. No arbitrary
  isomorphism or unspecified canonical map replaces this component formula.
- B is exactly `Γ(C.left, ⊤)`, whose commutative ring structure is already provided.
  `Nontrivial B` expresses nonzero. `@FiniteDimensional ... (Algebra.toModule ...
  C.hom.ΓAlgebra)` uses precisely the K-action induced by C's structure morphism.
  Explicit instance arguments avoid a hidden let binder or an unrelated scalar action.
- B is local: `IsLocalRing B`. Its unique maximal ideal is specified by
  `∀ I : Ideal B, I.IsMaximal ↔ I = RingHom.ker (finiteGroupIdentityEvaluation G)`.
  The evaluation is literally the pullback on global sections along
  `GrpObj.identityComponentOne G`, composed with `Scheme.ΓSpecIso` to K.
- The residue field is K by that evaluation: there exists a ring equivalence from
  `B ⧸ RingHom.ker (finiteGroupIdentityEvaluation G)` to K whose value on EVERY
  quotient class of b is evaluation of b. This fixes the equivalence, including its
  compatibility with K, since evaluation at this K-section retracts the structural K-map.
- d and q are `(GrpObj.identityComponent G).hom.finrankΓ` and `Nat.card H`.
  The final three conjuncts give `1 ≤ d`, `1 ≤ q`, and `G.hom.finrankΓ = d * q`.
  The definition of finrankΓ is Module.finrank with the same structural ΓAlgebra.

Dependency declarations read and used:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`
  (the recorded match explicitly includes this predicate, besides AlgebraicClosure).
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `CategoryTheory.GrpObj`;
  monoidal Mon/Cartesian Hom interfaces, `IsCommMonObj`, `IsMonHom`, `Hom.group`.
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents this exact specialization
  and supplies `IsSubgroupScheme`; its Morphisms.FiberDegree import supplies
  `Scheme.Hom.ΓAlgebra` and `Scheme.Hom.finrankΓ`.
- def-weil-pbc-constant-group-scheme: WeilConjectures.AlgebraicGeometry.ConstantGroupScheme,
  `constantGroupSchemeProjection`, `constantGroupSchemeIncl`,
  `constantGroupSchemeMultiplication`, with their original coproduct construction.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, its projections and lift; the Over cartesian tensor is this pullback
  (Mathlib.CategoryTheory.Monoidal.Cartesian.Over).
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, `Spec`, `Spec.map`;
  `Scheme.ΓSpecIso` in GammaSpecAdjunction identifies sections over Spec K with K.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion, `IsOpenImmersion`.
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic uses this in the existing
  `GrpObj.identityComponentOpens`, `identityComponent`, `identityComponentι`,
  `identityComponentOne`, `onePoint`, and `mulLeft`. Their full definitions were read;
  this construction retains the full open subscheme structure, including nilpotents.

The stated proof dependencies are imported: the existing affine/finite, pullback and
scheme coproduct APIs from Mathlib; QuasiFinite.Basic for finite discrete spectra;
Artinian.Module and HopkinsLevitzki for finite-dimensional and nilpotent local algebras;
Gluing for gluing and uniqueness; and
WeilConjectures.Mathlib.AlgebraicGeometry.AlgClosed.Basic for
`exists_comp_eq_id_of_isFinite`. The declaration docstring carries all six proof steps
and their node references, including the direct B tensor B argument of step 3.

Edge cases checked before writing:

- The trivial group: C = G = Spec K, B = K, I = 0, d = q = 1; translation formula is identity.
- A finite constant abelian group: C = Spec K and d = 1, while q is the group cardinality.
- α_p in characteristic p: C = G, H is trivial, B = K[t]/(t^p), I = (t), d = p, q = 1.
- μ_p in characteristic p: the full nonreduced open identity component is retained,
  giving d = p and q = 1. In characteristic prime to p, μ_p is constant over K,
  giving d = 1 and q = p.
- A product of a local finite commutative group and a constant group gives the stated dq.
- Empty G and empty H are excluded by the existing group unit over the nonempty Spec K,
  not by an extra nonempty hypothesis. No restriction on characteristic is imposed.
- Scheme, field and rational-point types all use the standard scheme universe u;
  the Hom type is Type u, so the constant scheme's Small.{u} requirement is automatic.

Searches:

1. msearch.py leanfinder, query: "A finite commutative group scheme over an algebraically
   closed field is the product of its connected identity component and the constant
   group scheme of its rational points". Eight Galois-category decomposition/Hom
   finiteness hits; no matching group-scheme statement.
2. msearch.py loogle, query: `"AlgebraicGeometry", "connectedComponent"`.
   Two hits: Scheme.Hom.connectedComponentsHomeomorph and its apply lemma, neither
   asserting a local–constant product.
3. msearch.py grep, query: `identityComponent|connectedComponent|localConstant`,
   subdirectory AlgebraicGeometry. Eight hits in Geometrically/Connected and
   Sites/ConstantSheaf, none a group-scheme product decomposition.
4. rg on lean/WeilConjectures and lean/Sheaf for identityComponent, connectedComponent,
   constantGroupScheme and local/constant group splits. Found and reused
   GroupScheme.Basic's identity component and ConstantGroupScheme's constant construction.
   Existing LocallyAlgebraicGroupIdentityComponent and GroupNeutralComponentTranslates
   give related component geometry but do not state this product or augmented local algebra.
   The exact blueprint id search in lean/WeilConjectures returned no declaration.
   Checked the DAG's recorded dependency declarations as well; no second definition needed.
5. Read the cited source directly with pdftotext: Milne, printed pp. 209–210,
   Propositions 11.1–11.3. Proposition 11.3 gives the semidirect splitting over a perfect
   field, which is the direct product in the present commutative algebraically closed case.

Validation: scompile.py compiled both the sandbox module and the actual library module
cleanly. The preliminary coprojection proof was replaced by the existing Sigma.ι_desc
identity term; no additional theorem or postponed construction was introduced.
No node fault or statement dispute was found. No new nodes or dependency repairs.

## Second reading by Q141

Independent clause-by-clause reading of the delivered statement against the node, its
stmt_dep records and Milne, Algebraic Groups (2017), Props 11.1–11.3 (pp. 209–210) and 2.37
(supplied by the maintainer's second reader; the delivery's own section was a re-reading in
the same worker session).

Node clauses and their Lean rendering:

1. K algebraically closed field [def-weil-field, def-weil-algebraic-closure]:
   `(K : Type u) [Field K] [IsAlgClosed K]`. No characteristic or perfectness assumption. Correct.
2. G finite commutative K-group scheme [def-sc-group-scheme]: `G : Over (Spec (.of K))`,
   `[GrpObj G] [IsCommMonObj G] [IsFinite G.hom]`, the recorded representation. No extra
   hypothesis; the `LocallyOfFiniteType`/`QuasiCompact` instances needed by
   `GrpObj.identityComponent` are inferred from `IsFinite`. Correct.
3. C = connected component of the identity with its open-and-closed subscheme structure:
   upstream `GrpObj.identityComponent G` = `Over.mk ((identityComponentOpens G).ι ≫ G.hom)`
   on `connectedComponent (GrpObj.onePoint G)` (GroupScheme/Basic.lean), the full open
   subscheme (nilpotents kept); clause `IsClopen (connectedComponent (GrpObj.onePoint G))`.
   Correct.
4. C finite, connected, commutative subgroup scheme: `IsFinite C.hom`, `ConnectedSpace C.left`,
   `IsCommMonObj C` for the upstream restricted `GrpObj` instance (unit/mul/inv lifted through
   the open immersion), `IsSubgroupScheme (GrpObj.identityComponentι G)` (GroupScheme/Defs:
   IsMonHom + injectivity on R-points). Correct.
5. H = G(K) finite: `Finite (𝟙_ (Over (Spec (.of K))) ⟶ G)`, the K-points with the recorded
   `Hom` commutative group. Correct.
6. H_K = ∐_{h∈H} Spec K with addition induced from H [def-weil-pbc-constant-group-scheme]:
   `finiteGroupConstantPoints G` = `Over.mk (constantGroupSchemeProjection (Spec K) (Additive H))`
   (packaging only). The group structure is `∃ gH : GrpObj _` with
   `(μ[…]).left = constantGroupSchemeMultiplication …`; that recorded map is the `choose` of an
   existence whose component formula (pair component (e,e') → component e+e') pins it on a
   jointly epimorphic open cover, so it is the canonical law, and the unit/inverse of gH are
   determined by the group axioms. Commutativity recorded too. Correct.
7. φ : C ×_K H_K → G, on the h-component translation by h, an isomorphism of group schemes:
   `∃ φ : C ⊗ H_K ≅ G, IsMonHom φ.hom ∧ ∀ h, lift (𝟙 C) (toUnit C ≫ incl h) ≫ φ.hom =
   identityComponentι G ≫ mulLeft G h.toMul`. The cartesian tensor in Over is the fibre product
   [def-pc-fibre-product]; the maps `lift (𝟙 C) (toUnit C ≫ incl h)` are the component
   inclusions C = C ×_K Spec K, which cover C ×_K H_K, so φ is pinned on every component (not
   an arbitrary iso). Left translation = the node's translation by commutativity. The inverse of
   a monoid-hom iso is a monoid hom, so this is an iso of group schemes. Correct.
8. B = Γ(C, O_C) nonzero, finite-dimensional, local: `Nontrivial Γ(C.left, ⊤)`,
   `FiniteDimensional K _` with the module structure of `C.hom.ΓAlgebra` (the structural
   K-action, FiberDegree.lean), `IsLocalRing Γ(C.left, ⊤)`. Correct.
9. Unique maximal ideal I = ker ε, ε evaluation at the identity: `∀ I, I.IsMaximal ↔
   I = RingHom.ker (finiteGroupIdentityEvaluation G)`, where ε = `(identityComponentOne G).left.appTop
   ≫ ΓSpecIso K` (pullback along the unit section of C). Correct.
10. Residue field K: `∃ e : B ⧸ ker ε ≃+* K, ∀ b, e (mk b) = ε b`. The equivalence is pinned by ε.
    Correct.
11. d = dim_K B, q = |H|, d,q ≥ 1, dim_K Γ(G, O_G) = dq: `1 ≤ C.hom.finrankΓ`,
    `1 ≤ Nat.card H`, `G.hom.finrankΓ = C.hom.finrankΓ * Nat.card H`; finrankΓ is
    `Module.finrank` for the same ΓAlgebra. Correct.

Edge cases: trivial G (C = G = Spec K, d = q = 1); constant groups (d = 1); α_p, μ_p in
characteristic p (C = G, nonreduced B, q = 1); μ_n in characteristic prime to n (d = 1,
q = n). All covered with no extra hypothesis; empty G impossible by the unit section. All objects
in universe u; H : Type u so the constant scheme's `Small.{u}` is automatic.

One definition per notion: identity component, translation, subgroup scheme, constant scheme
and its law, finrankΓ/ΓAlgebra are the recorded upstream declarations; the three new
declarations are transparent packagings (Over.mk of the recorded projection, Over.homMk of the
recorded coprojection, appTop of the recorded unit section) with source and blueprint docstrings.
The only other identity evaluation found (`GroupScheme.Lie.LocalPoints.counit`) is on the stalk at
the identity, a different object. No hollow definition; the only postponed proof is the theorem's
`sorry`; the theorem docstring carries all six proof steps.

Mismatches found: none in the Lean or the records. Changed: this section only (replacing the
same-session re-reading).
