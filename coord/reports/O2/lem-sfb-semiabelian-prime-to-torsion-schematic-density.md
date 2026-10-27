## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianPrimeToTorsionSchematicDensity`
states `AlgebraicGeometry.semiabelian_isIso_of_contains_primeToTorsion`.
Its sole theorem has proof `sorry`; there are no new definitions, helper theorems,
additional nodes, dependency repairs, or changes to the mathematical statement.
The node copy differs only in `lean`.

The following matches every hypothesis and clause of the node:

| Node text | Lean rendering |
| --- | --- |
| An algebraically closed field F | `(F : Type u) [Field F] [IsAlgClosed F]` |
| A group scheme G over Spec F | `(G : Grp (Over (Spec (.of F))))`; `G.X.hom` is its structure morphism and the bundled group supplies `GrpObj G.X` |
| Commutative | `[IsCommMonObj G.X]`, using the existing multiplication-commutes-with-swap predicate |
| Smooth | `[Smooth G.X.hom]` |
| Separated, meaning closed diagonal | `[IsSeparated G.X.hom]`, whose defining field is `IsClosedImmersion (pullback.diagonal G.X.hom)` |
| Finite type | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, precisely the conjunction recorded by def-weil-finite-type-morphism |
| Semiabelian geometric fibres | `(hG : HasSemiabelianGeometricFibres G)`; this is the shared definition with a split torus kernel, abelian quotient, and fppf local surjectivity on each geometric fibre |
| Positive integer n | `∀ (n : ℕ), 0 < n → ...` |
| The image of n in F is nonzero | `(n : F) ≠ 0` |
| Multiplication by n with the given group law | `(𝟙 G.X ^ n).left`; the group-scheme dependency explicitly identifies the power in the group of morphisms with the n-fold sum |
| An F-rational point x | `x : G.X.hom.fieldPoints F`, the existing section type, with underlying scheme morphism `x.1` |
| x is killed by n | `x.1 ≫ (𝟙 G.X ^ n).left = (MonObj.one (X := G.X)).left`; the right side is the identity section from the tensor unit of `Over (Spec F)`, whose underlying scheme is Spec F |
| A closed subscheme of G | `{Z : Scheme.{u}} (i : Z ⟶ G.X.left) [IsClosedImmersion i]`; Z carries no artificial group structure |
| Every such point factors through Z | `∃ z : Spec (.of F) ⟶ Z, z ≫ i = x.1` in `hT` |
| A point killed by some allowed n | Universally quantifying n and then x gives exactly the assertion for all points with an allowed annihilator: each witness n triggers its factorization, and conversely the original assertion supplies every instance of `hT` |
| Z=G as a closed subscheme | `IsIso i`, for this specific closed immersion, expresses that it is the whole closed subscheme; an unrelated abstract isomorphism or equality of supports would not suffice |
| Rank zero and zero-dimensional abelian quotients allowed | No dimension or positive-rank binder is imposed. The recorded semiabelian definition allows `r : ℕ`, hence r=0, and its abelian variety has no positive-dimension condition |

A lift z need not carry an additional condition over F: its composite with
`i ≫ G.X.hom` equals `x.1 ≫ G.X.hom`, hence the identity, since x is a rational
section. Thus the displayed scheme factorization is exactly factorization over F.

Statement dependencies were read in the DAG and their source declarations/docstrings:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic,
  `IsAlgClosed` (the node's Mathlib match explicitly records this component,
  alongside `AlgebraicClosure` and `IsAlgClosure`). No particular presentation as
  the algebraic closure of another field is imposed.
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `Scheme`, `Scheme.Hom`.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `Grp`, `GrpObj`,
  and Mathlib.CategoryTheory.Monoidal.Mon, `IsCommMonObj`; the recorded
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents the exact
  group-scheme specialization and multiplication-by-n convention. Opening the
  public `MonObj` scope activates the existing group-of-morphisms instance.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`, and Morphisms.QuasiCompact, `QuasiCompact`.
- def-sfb-semiabelian-geometric-fibres:
  Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres,
  `HasSemiabelianGeometricFibres`, read in full with its geometric base change,
  actual kernel square, and fppf-locally surjective quotient.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `IsClosedImmersion`.
- def-pc-rational-point: WeilConjectures.AlgebraicGeometry.DensePoints,
  `Scheme.Hom.baseChangeFieldPoint` and its docstring identifying rational points
  with the existing `Scheme.Hom.fieldPoints` sections. No new notion of a point
  is introduced and no dependency record needs repair.

All recorded proof modules are plain imports: Mathlib.AlgebraicGeometry.Properties
(`IsReduced`), Mathlib.AlgebraicGeometry.Fiber (`Scheme.Hom.fiber`),
Mathlib.CategoryTheory.Yoneda (`Yoneda.fullyFaithful`),
WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
(`closedSubscheme_baseChange_ideal_image`),
Sheaf.RingTheory.ReducedIdealsZeroIntersection
(`Ideal.reduced_ideals_zero_intersection`),
Sheaf.AlgebraicGeometry.AbelianVariety.PrimeToTorsionDense
(`IsAbelianVariety.eq_univ_of_contains_primeToTorsion`), and
WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
(`Smooth.geometricallyReduced`). The other proof dependencies already appear as
public statement imports. The two proof-only nodes
lem-sfb-smooth-affine-group-torsor-representability and
lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density have no Lean record
in the read repository and therefore no module to import; their uses remain in
the proof docstring and unchanged DAG proof_deps. They supply no missing notion
in this theorem's signature.

Edge cases checked before writing:

- n=0 is excluded explicitly, including in characteristic zero.
- n=1 is allowed and forces the identity rational point to factor through Z.
- In characteristic p, exactly the positive n not divisible by p have nonzero
  image in F; in characteristic zero every positive n is allowed.
- Rank zero allows an abelian variety; abelian quotient dimension zero allows a
  torus; both zero allows Spec F with its trivial group. The statement retains all.
- The empty closed subscheme cannot satisfy hT, since the identity is killed by 1.
- An empty group scheme over a field cannot have the required identity section,
  so the bundled group does not exclude an allowed case.
- No finite, reduced, smooth, or subgroup condition is imposed on Z. Smoothness
  of G provides reducedness in the proof rather than as an added hypothesis.
- `IsIso i` retains the scheme structure. For a closed immersion this is
  equivalent to its closed subobject being the top subobject.
- All field/scheme objects use the shared universe u, as the dependency definition
  requires. This introduces no smaller independent universe of test fields.

Searches for an existing exact declaration (all through the prescribed msearch.py
or read-only rg):

1. LeanFinder: "Prime to characteristic torsion rational points of a semiabelian
   variety are schematically dense". Eight hits, for dense rational-map domains,
   dominant scheme morphisms, and a circle group; none states this theorem.
2. Loogle: "GrpObj, IsClosedImmersion". Zero hits; its index does not recognize
   GrpObj. This unavailable-name outcome was retained rather than treated as a match.
3. Mathlib grep through msearch.py, subdirectory AlgebraicGeometry:
   `semiabelian|Semiabelian|torsion.*[Dd]ens|[Dd]ens.*torsion`. Zero hits.
4. LeanSearch: "Schematic density of prime to characteristic torsion in semiabelian
   group scheme". Eight hits about arithmetic density, characteristic, or abstract
   group torsion; no match.
5. The same semiabelian/torsion-density regex in lean/WeilConjectures and lean/Sheaf
   found the shared semiabelian definition, abelian torsion-density input, and
   other semiabelian extension/ampleness theorems. None is the present statement.
6. The item's full blueprint id in lean/WeilConjectures: no match.
7. The proposed full theorem name in Mathlib, lean/WeilConjectures, and lean/Sheaf,
   and `semiabelian|Semiabelian` in dag/lean_names_upstream.json: no match.

The local Milne Algebraic Groups PDF was opened with pdftotext: Theorem 12.32 is
schematic density for smooth multiplicative-type groups, while Aside 12.51 says
prime-to-characteristic torsion is dense for toroidal groups and that the property
is preserved by extensions. These support exactly the torus and semiabelian route
in the accepted six-step DAG proof, not a spurious verbatim Milne theorem.
The theorem's docstring carries all six proof steps and their named inputs.
No STATEMENT-DISPUTED issue or node correction was needed.

Validation: the prescribed scompile.py compiled both the sandbox module and its
library-path version cleanly (2.5 s and 2.3 s), with no warnings. The first probe
identified the required public `MonObj` scope for the existing power instance;
opening it fixed the issue without any helper definition or statement change.
The module is in module mode, has autoImplicit false, explicitly binds universe u,
and has no line longer than 100 characters. The Lean record copies its signature
verbatim. Dry-run and delivery results are recorded below once obtained.

## Second reading by O2

The dispatcher instruction prohibits starting another agent, so this section is
an explicit separate self-check, not a claim of independent review; the
maintainer's independent delivery review remains applicable. Reopened the node
and the complete Lean module and checked each row above against the actual
signature. In particular, hT ranges over rational sections, its killed equation
uses the given group law, the factorization is a scheme morphism equality, and
the conclusion concerns the actual closed immersion. The positive integer and
nonzero-in-F conditions are both present. Neither Z nor the semiabelian rank
acquires an additional condition. All statement dependencies use their existing
interfaces. No mathematical mismatch was found; the only elaboration repair was
the scope opening already described. No new or dependency nodes need a second
reading.

Dry run: deliver2.py --no-push returned `OK (dry run): commit bb22bc8f328
passes the preflight and compiles; nothing pushed`. Only the theorem module,
item node record, and worker report were staged.
