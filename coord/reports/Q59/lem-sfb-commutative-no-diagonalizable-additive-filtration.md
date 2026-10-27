## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CommutativeAdditiveFiltration` states
`AlgebraicGeometry.commutative_no_diagonalizable_additive_filtration`. Its sole proof is
`sorry`; no definition or instance is introduced. Read Milne, Algebraic Groups (2017),
Theorem 16.13(a),(b), printed p.328 (PDF p.340), and Proposition 14.21 and its proof,
printed pp.284--285 (PDF pp.296--297). These apply to full affine algebraic group schemes;
Example 14.19 explicitly includes alpha_p and the constant group Z/pZ.

Clause correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- k-group scheme: `G : Grp (Over (Spec (.of k)))`; its structure map is `G.X.hom`.
- Commutativity: `[IsCommMonObj G.X]`.
- Affineness: `[IsAffine G.X.left]`.
- Finite type: `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, precisely the
  conjunction recorded by def-weil-finite-type-morphism.
- A diagonalizable group Spec k[M] with the specified basis and coproduct is the existing
  `diagonalizableGroup k M`; `[AddCommGroup M] [AddGroup.FG M]` imposes precisely finite
  generation as an abelian group. Its definition uses `AddMonoidAlgebra` with the
  canonical Hopf coproduct, counit and antipode, through `hopfSpec`.
- Every diagonalizable closed subgroup is trivial: `hdiag` quantifies over all such M,
  every group homomorphism `i : diagonalizableGroup k M ⟶ G`, and its
  `IsClosedSubgroupScheme i.hom.hom` property, and concludes
  `IsIso (diagonalizableGroup k M).X.hom`. This is triviality over Spec k. An arbitrary
  diagonalizable subgroup is isomorphic to one of these models; composing its inclusion
  with that group isomorphism gives exactly this test, including nonreduced subgroups.
- Nonnegative length: `s : ℕ`.
- Chain objects G_0,...,G_s: `H : Fin (s + 1) → Grp (Over (Spec (.of k))))`.
- Closed subgroup inclusions in G: `ι j : H j ⟶ G` and
  `∀ j, IsClosedSubgroupScheme (ι j).hom.hom`.
- Successive inclusions: `a j : H j.castSucc ⟶ H j.succ`, their
  `IsClosedSubgroupScheme` conditions, and `a j ≫ ι j.succ = ι j.castSucc`.
  This equation ties the successive chain to the specified subgroups of G.
- G_0 = 1: `IsIso (H 0).X.hom`, identifying it with Spec k over k. The group law on a
  terminal object is unique, so this is the trivial group scheme, not just one k-point.
- G_s = G: `IsIso (ι (Fin.last s)).hom.hom.left`. This is the inclusion itself being
  an isomorphism, so its image as a subgroup is all of G.
- Affine finite-type factors: `Q : Fin s → Grp (Over (Spec (.of k))))`, and, for every j,
  `IsAffine (Q j).X.left`, `LocallyOfFiniteType (Q j).X.hom`, `QuasiCompact (Q j).X.hom`.
- Quotient group homomorphisms: `q j : H j.succ ⟶ Q j` are morphisms in bundled `Grp`.
- Faithfully flat: `Flat (q j).hom.hom.left ∧ Surjective (q j).hom.hom.left`.
- Finitely presented: `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`
  on the same scheme map, as in def-sbc-locally-finite-presentation's comparison clause.
- Scheme-theoretic kernel H_(j-1) of q_j: `IsFppfGroupQuotient (a j) (q j)` contains
  `IsPullback (a j).hom.hom (toUnit ...) (q j).hom.hom η[...]`. Thus it records the
  specified inclusion as the fibre over the identity, including infinitesimal structure.
- Closed group embedding Q_j -> Ga: `b j : Q j ⟶ Grp.mk (StandardGroupSchemes.additive k)`
  and `IsClosedSubgroupScheme (b j).hom.hom`. The existing Ga has coordinate algebra
  k[y], coproduct y⊗1+1⊗y, counit 0 and antipode -y.
- Representation of the fppf sheafification of R ↦ G_j(R)/G_(j-1)(R):
  `IsFppfGroupQuotient (a j) (q j)` includes the pointwise coset coequalizer and a map
  from it to `yoneda.obj (Q j).X`, whose composite is the specified q_j and which has
  bijective precomposition into every fppf sheaf. It also records fppf local surjectivity,
  representable sheafness and the canonical torsor coordinates (g,n) ↦ (g,g a(n)).
  These are the existing general presentation of this quotient, rather than an unrelated
  isomorphism or abstract group quotient. Restriction to affine test schemes gives the
  algebra-valued formulation in the node; affine fppf refinements give the same sheaf.
- No smoothness or connectedness appears among the hypotheses. `Fin s` is empty for s=0;
  for trivial G choose a one-object chain and no a,Q,q,b data. Endpoint equations
  are expressed up to the canonical categorical meaning of equality of subgroup schemes.

Dependencies read and used (module, declarations):

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (splitting, equivalently every nonconstant polynomial has a root).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, group-object morphisms;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsCommMonObj`, `IsMonHom`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`; the recorded group-scheme dictionary.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, inherited
  from the closed-subgroup predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `QuasiSeparated` is the remaining global finite-presentation condition.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.additive`,
  `StandardGroupSchemes.additiveGroup`, `additiveComul`, `additiveCounit`, `additiveAntipode`.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`: algebra tensor product,
  `includeLeft`, `includeRight`, `productMap`, and `ext`, as used by the dependency
  constructions of group laws and coordinate comultiplications.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Over`: its slice over Spec k.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`. The quotient API uses their universal property directly,
  avoiding any separate choice of a sheafification object.
- Added already-landed definition dependencies `def-sfb-diagonalizable-group`, module
  `Sheaf.AlgebraicGeometry.DiagonalizableGroup`, declaration `diagonalizableGroup`, and
  `def-sfb-fppf-group-quotient-presentation`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`, declaration
  `IsFppfGroupQuotient`. No new node or duplicate definition is needed.
- Proof-only import `Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization`,
  `algebraicGroup_homomorphism_factorization`. The other non-definition proof dependencies
  have no recorded Lean declaration in the read repository and hence no import yet.

Edge checks: the empty scheme cannot carry the group unit over a nonzero field, so the
hypotheses introduce no excluded empty group. The trivial group permits s=0, with both
endpoints the same object. Repeated chain entries and trivial quotient factors are allowed
(the node does not require strict inclusions). Alpha_p and the constant group Z/pZ in
characteristic p are included as possible additive factors. Mu_p is tested by hdiag using
M=Z/pZ: its single geometric point does not incorrectly make its structure morphism an
isomorphism. Characteristic zero is also included. `M : Type u` is sufficient for every
finitely generated abelian group, which is small in any universe after replacement by an
isomorphic group; no independent smaller test-algebra universe is used.

Searches actually run with msearch.py for this item:

- LeanFinder: "A commutative affine group scheme without nontrivial diagonalizable
  subgroups has a finite filtration with closed additive group subgroup quotients".
  Eight hits concerning abstract/profinite group quotients and affine finite morphisms;
  no group-scheme filtration theorem.
- Loogle: `"GrpObj", "IsCommMonObj"`. Three hits: a cocommutative Hopf algebra instance,
  the conjugation formula for a commutative group object, and CommGrpObj's projection;
  none states the requested filtration.
- Mathlib grep: `diagonalizable|Diagonalizable|unipotent`, subdirectory AlgebraicGeometry.
  Zero hits.
- LeanSearch: "A commutative affine algebraic group with no nontrivial diagonalizable
  subgroup has a finite filtration with quotients isomorphic to closed subgroups of the
  additive group scheme". Eight hits, including abstract simple additive groups,
  `AddMonoidAlgebra.finiteType_iff_group_fg`, and module filtrations; no exact theorem.
- `rg` in `lean/WeilConjectures` for `diagonalizableGroup|no_diagonalizable|additive_filtration`:
  no hits; also no hit for this node id by `grep -rn`.
- `rg` in `lean/Sheaf/AlgebraicGeometry`: located the existing `diagonalizableGroup`,
  `StandardGroupSchemes.additive` and `IsFppfGroupQuotient` definitions, but no theorem
  with this statement. Read all three definitions in full and their docstrings.
- `rg` in `dag/lean_names_upstream.json` for the proposed name and `diagonalizableGroup`:
  no hits. DAG lookup confirmed both definition nodes already own the reused declarations.

No statement correction and no statement dispute. Only `lean` and the authorized addition
of the two landed definition ids to `stmt_deps` change in the item's JSON.

Validation: scompile.py compiled both the sandbox and actual library module forms cleanly.
The first probe caught the constructor spelling `Grp.of`; it was corrected to Mathlib's
actual `Grp.mk`. There are no diagnostic commands or scratch declarations in the module.

## Second reading by Q59

A second pass by the assigned worker opened the node and the finished module together;
the maintainer performs the independent review after delivery. Checked hdiag against the
node's full group-scheme triviality condition, not merely geometric-point triviality;
the structure-morphism `IsIso` correctly rejects mu_p. Checked all finite indices:
`castSucc` is G_(j-1), `succ` is G_j, and `Fin.last s` is G_s. The same `a j` is used in
both the inclusion compatibility and the quotient's cartesian kernel square; the same
`q j` occurs in the flatness, presentation, and sheafification assertions. Checked the
existing quotient definition's actual unit, torsor projections and coequalizer against
the sheaf quotient clause. Checked affineness and finite type of every Q_j separately.
The two endpoints are isomorphisms through the specified structure/inclusion maps, so
no unrelated isomorphic subgroup can satisfy the chain endpoint. No clause or hypothesis
was missing on this second pass, and no further statement change was made. The only compile
repair was the constructor spelling already noted above. The two added stmt_deps refer to
existing definition nodes; no theorem was inserted as a statement hypothesis.
