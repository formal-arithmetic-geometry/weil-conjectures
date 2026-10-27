## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnitriangularCoordinateFiltration` states
`AlgebraicGeometry.unitriangular_coordinate_filtration`, with its proof `sorry`. There are no
new definitions, no dependency repairs, and no statement corrections. The theorem presents
the matrix subgroups existentially, with their exact functors of points; it does not choose
unspecified objects in definitions. This retains the scheme structure, including on nonreduced
algebras. All universes and variables are explicit and `autoImplicit` is false.

Source checked: Milne, Algebraic Groups (2017), Example 6.49(a)--(c), printed pp.136--137
(PDF pp.148--149). The displayed ordering, equations, normality, additive quotients and
conjugation character are precisely those of the node. The latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was read; this is a supporting input, not that unit's own statement.

Hypothesis and clause correspondence:

- A field k and n >= 1 are `(k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n)`.
- The length m=n(n-1)/2 is used literally in every `Fin` bound. The equivalence `C` from
  `Fin m` to `{p : Fin n × Fin n // p.1 < p.2}` enumerates every strict upper pair exactly
  once. The first conjunct orders it by increasing difference, then increasing row.
  Indices are zero-based, so Lean `C r` is the paper's C_(r+1); subtracting one from both
  matrix indices preserves this ordering.
- The invertible upper triangular group is `B` with `β` into the recorded general linear
  group on `LinearGroupSchemes.Index n`. `IsClosedSubgroupScheme β.hom.hom` is the closed
  subgroup condition. For every commutative k-algebra and every GL-point x, existence of
  its lift to B is equivalent to all below-diagonal matrix entries being zero. Thus B is
  exactly the stated group scheme, not an arbitrarily named group or abstract group of
  rational points. `LocallyOfFiniteType B.X.hom ∧ QuasiCompact B.X.hom` records finite type.
- `H : Fin (m+1) → Grp (Over (Spec (.of k)))` with `inc r : H r ⟶ B` gives every U^(r).
  The lift criterion for b in B is exactly diagonal entries one and the coordinates C_l
  zero for l.val < r.val. In the paper's one-based numbering this is l <= r. Because this
  is required for every algebra, it specifies the equations scheme-theoretically.
- Each `inc r` is both `IsClosedSubgroupScheme` and `IsNormalSubgroupScheme`; the latter
  is the recorded definition testing normality on every k-algebra. Finite type of each
  H r is the conjunction of local finite type and quasi-compactness of its structure map.
- `H 0` has no killed strict upper coordinates and is precisely U_n by the lift criterion.
  `IsIso (H (Fin.last m)).X.hom` says the last term is the trivial group scheme Spec k.
- `a r : H r.succ ⟶ H r.castSucc`, its closed-subgroup property, and
  `a r ≫ inc r.castSucc = inc r.succ` retain the actual consecutive subgroup inclusions.
- `p r` is a morphism in `Grp` to the recorded additive group. The point identity
  `x ≫ (p r).hom.hom = additiveCoordinatePoint ... (matrix entry at C r)` fixes it as
  precisely the coordinate projection, including on nilpotent-valued points.
- `Flat` and `Surjective` on its underlying scheme map are faithful flatness;
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` are finite presentation
  as defined by def-sbc-locally-finite-presentation.
- `IsFppfGroupQuotient (a r) (p r)` includes the cartesian kernel square, so the kernel is
  the specified H r.succ with its actual embedding, not just an abstractly isomorphic
  group. It also includes the coset-presheaf coequalizer and sheafification universal
  property into h_Ga. Thus it is exactly the asserted represented fppf quotient
  isomorphism, with the induced quotient map retained. This definition additionally
  packages the canonical torsor identity, a consequence of this same quotient presentation.
- `delta : Fin n → (B ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))` consists of the
  components of B -> Gm^n. Each is a group-scheme homomorphism; its coordinate value is
  required to equal the corresponding diagonal matrix entry on every algebra.
- The conjugation clause gives the unique lift y of b*x*b^-1 to the preceding filtration
  term and requires its p-coordinate to be the product of delta_i(b), delta_j(b^-1),
  and x_ij. Since delta_j is a group homomorphism, its value on b^-1 is the unit inverse
  of b_jj. This is p(bub^-1)=(b_ii*b_jj^-1)*p(u). Expressing the multiplier through
  delta_i and delta_j states its factorization through the diagonal and exactly the
  character (t_i)*(t_j)^-1, without introducing division on a general ring R.
- The penultimate conjunct explicitly says conjugation by every H 0-point preserves
  p, i.e. U_n acts trivially on every additive quotient. This also states centrality.
- The final implication `n = 1 → IsIso (H 0).X.hom`, together with the length bounds,
  retains the length-zero case and U_1=1.

Declarations used (full signatures and docstrings read in the indicated sources):

- `Field`, Mathlib.Algebra.Field.Defs; the commutative k-algebra structures are Mathlib's.
- `CategoryTheory.GrpObj`, `Grp`, and group-object morphisms from
  Mathlib.CategoryTheory.Monoidal.Grp; subgroup notions from
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear, exposed through the
  dependency's recorded Sheaf.AlgebraicGeometry.LinearGroupSchemes module; its
  `LinearGroupSchemes.Index` is used verbatim for the base-field universe convention.
- `StandardGroupSchemes.affine`, `additive`, `multiplicative` and their group structures,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes (recorded dependency def-sc-gm-ga).
- `StandardGroupSchemes.additiveCoordinatePoint` and `multiplicativeCoordinateValue`,
  Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient. Their existing definition
  node def-sfb-standard-group-coordinate-points is added to stmt_deps; neither is copied.
- `IsFppfGroupQuotient`, Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry.
  Its existing definition node def-sfb-fppf-group-quotient-presentation is added to
  stmt_deps. The definition includes the actual kernel square and quotient universal arrow.
- `Spec` and `Spec.map`, Mathlib.AlgebraicGeometry.Scheme, through the recorded group
  modules; `IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion;
  `LocallyOfFiniteType` / `QuasiCompact`, Morphisms.FiniteType / Morphisms.QuasiCompact;
  `Flat`, Morphisms.Flat; `LocallyOfFinitePresentation`, Morphisms.FinitePresentation;
  `QuasiSeparated`, Morphisms.QuasiSeparated. These retain the recorded notions.
- Fppf and fpqc topologies, Mathlib.AlgebraicGeometry.Sites.Fpqc; the over-site and
  sheafification universal property are used through `IsFppfGroupQuotient`, whose
  exact definition was read. `presheafToSheaf` and its adjunction are the recorded
  sheafification notion; no replacement sheafification is introduced here.
- Proof imports retain the Mathlib affine/separated permanence and polynomial flatness
  material named by proof_deps. The source/group modules already expose affine spectrum,
  MvPolynomial, and the fppf/fpqc representable-descent API. No proof dependency is unstated.

Edge cases checked before writing: n=1 has no strict upper pairs and no quotient data;
n=2 has the single additive coordinate and weight b_11/b_22; n=3 has C=(12,23,13),
so the cross term u_12*v_23 is killed before projecting to the third coordinate. The last
projection r=m has no remaining polynomial variables and is an isomorphism. Arbitrary
characteristic, nonperfect fields, nonreduced test algebras and the zero test algebra
are included. No inverse of a general ring element is used: the inverse diagonal entry
comes from the inverse group point. At r=0 the empty equation list yields U_n, and at
r=m all upper entries and the below-diagonal entries are zero with diagonal ones.
The existential point descriptions are exact closed-subfunctor descriptions, not
conditions only on field-valued points; nilpotents are not lost.

Searches made:

- msearch.py leanfinder: "Upper unitriangular group scheme coordinate normal filtration
  additive quotients diagonal conjugation weights". Eight hits concerned Lie weight
  spaces and Geck matrices, not this scheme filtration.
- msearch.py loogle: "Matrix.BlockTriangular, GeneralLinearGroup". No hits; the search
  service did not recognize the short identifier GeneralLinearGroup.
- msearch.py grep: "unitriangular|Unitriangular|upperTriangular". Twenty-five hits were
  matrix triangularity, determinants and modular cusp calculations, not this statement.
- msearch.py leansearch: "Unitriangular matrix group scheme has coordinate filtration
  with additive quotient groups". Eight hits concerned ideal filtrations, uniform matrix
  groups and filtered colimits, with no matching theorem.
- rg in lean/WeilConjectures and lean/Sheaf for unitriang/Unitriang/upperTriang/
  UpperTriang/triangular.*Scheme/Triangular: no coordinate filtration declaration;
  project hits were theorems mentioning it in their proof plans. The general linear
  group and standard additive/multiplicative groups were reused.
- grep -rn for the exact item id in lean/WeilConjectures: no matches.
- rg for unitriangular/Unitriangular in dag/lean_names_upstream.json: no match.
- rg for IsFppfGroupQuotient in lean/Sheaf/AlgebraicGeometry/GroupScheme and dag/nodes
  found the existing definition node, which is reused, as is the existing standard
  coordinate-points definition node. No new nodes or helper definitions are necessary.

No STATEMENT-DISPUTED flag or source fault was found. The two added dependency ids already
have published Lean records; the item's statement, proof and all other original fields
are unchanged. Independent mathematical review is left to the maintainer as specified
by the dispatcher; no second worker was started and no independent reading is claimed.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
