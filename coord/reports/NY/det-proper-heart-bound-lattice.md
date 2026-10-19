## Worker report

Statement-only delivery of `det-proper-heart-bound-lattice` in
`lean/Sheaf/Paper/ProperHeartBoundLattice.lean`, declaration
`AlgebraicGeometry.ProEtale.properHeartBoundLattice`. The only postponed proof is this
named theorem, with `sorry`. Its docstring carries the seven current DAG proof steps.
No definition, node statement, or dependency record is changed; no new node is needed.

I read the current item, both statement-dependency records and declarations, the resolved
stage-1 repair note, the main-20261015 lattice statement and proof, and the torsion module.
The repair note is stage 1, resolved: its revised seven-step proof (including the separate
inverse-image/restriction comparison) is retained verbatim in the node. There is no released
stage-2 binding to reintroduce.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]` |
| Its valuation ring O_E | `DerivedNakayama.integerRing ℓ E`, the continuous condensed valuation ring built from `Padic.coefficientExtensionIntegers`, with its spectral absolute-value topology, not a discrete constant ring |
| A uniformizer pi_E | Auxiliary proof notation only: the conclusion contains no pi_E. The existing coefficient extension and reduction interface supplies its canonical uniformizer ideal; this theorem neither changes the ring nor imposes a choice of a new ring or lattice. It holds for any uniformizer because the asserted group is independent of that choice. |
| Field k of positive characteristic | `(k : Type u) [Field k] (hchar : ringChar k ≠ 0)`; for a field its nonzero ring characteristic is a positive prime |
| ell invertible in k | `(hell : ringChar k ≠ ℓ)`, equivalent for prime ell in a field of positive characteristic |
| X,Y separated finite-type k-schemes | `X.Over`, `Y.Over`, and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on their structure arrows to `Spec (.of k)` |
| Proper k-morphism p | `(p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]` |
| Integer d bounding geometric fibres | `(d : ℤ)` and `hd`; the geometric fibre is the pullback along the algebraic closure of each residue field, exactly as in the torsion declaration. In the ordered dimension type `WithBot ℕ∞`, the bound is `if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞)`. A negative integer bound means the fibre must be empty; for nonnegative d this is the ordinary dimension inequality. Geometric dimension is independent of the chosen algebraically closed extension. |
| Affine weakly contractible pro-etale V -> Y | `(V : Y.ProEt) [IsAffine V.left]` and `(hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)` |
| X_V = X x_Y V and its projection to X | `pullback p V.hom` and `pullback.fst p V.hom` |
| a : S -> X locally closed | `(j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]`, with `a = j ≫ i`. This is the factorization used in the retained torsion situation. Every locally closed immersion has this form. No density condition on the factorization is needed for the same a_!. |
| S in the same finite-type k-setting, a a k-morphism | `S.Over`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on `S ↘ Spec (.of k)`, and `[(j ≫ i).IsOver (Spec (.of k))]`. Sbar has its induced k-structure through its closed immersion into X and is finite type automatically. |
| L_0 over the pulled-back O_{E,S} | `(L : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) S)` |
| L_0 lisse finite free | `hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L`; its recorded definition uses a pro-etale cover and `Mod.IsFree`, whose rank is a natural number and may vary on the cover |
| Locally closed extension a_! = i_* j_! | `((torsionLocallyClosedExtension ℓ E j i).obj L)`, using the dependency's actual composite functor |
| Restriction of that module to X_V | Apply `Scheme.proEtaleSheafInverseImage (pullback.fst p V.hom) Ab.{u + 1}` to its underlying abelian sheaf `.X`. The recorded object-inverse-image comparison identifies this canonical inverse image with restriction to the slice. Thus the integral ring is restricted, never replaced by a discrete constant coefficient. |
| Pro-etale H^q and its vanishing | Place the restricted sheaf in degree zero with `DerivedCategory.singleFunctor _ 0`, apply `rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)`, and then `DerivedCategory.homologyFunctor Ab.{u + 1} q`; the conclusion is `IsZero` of that abelian group. Cohomology of a module is cohomology of its underlying abelian sheaf. |
| q > 2d+1 | `(q : ℤ) (hq : 2 * d + 1 < q)`; the inequality is strict, with no assertion at the borderline |
| No finite-type or Noetherian condition on V or X_V | Neither `V.left` nor `pullback p V.hom` has such a binder. No nonemptiness hypothesis is imposed anywhere. |

Dependency declarations used:

- `Sheaf.Paper.ProperHeartBoundTorsion`:
  `AlgebraicGeometry.ProEtale.torsionLocallyClosedExtension` and the statement/proof input
  `AlgebraicGeometry.ProEtale.properHeartBoundTorsion`. Its imports expose
  `Sheaf.Paper.DerivedNakayamaResolution` (`DerivedNakayama.integerRing`),
  `Sheaf.Paper.ModuleObjects` (`pulledBackModuleObjects`),
  `Sheaf.Paper.CoefficientHeartCommonStratification` (`IsLisseCoefficientModule`),
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (`Scheme.proEtaleSheafInverseImage`),
  and the finite-coefficient derived global sections declaration below. These are used,
  never copied or replaced.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, the record for
  `sk-def-sfb-dc-setting`. I read its local side source and requested the current source
  with `scompile.py --source`. The setting has explicit binders, as the record prescribes;
  a compactification is not additional input to the lattice theorem.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.rightDerivedGlobalSections`; read the current wrapper source.
  This is the total right derived functor of the actual global-sections functor.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, with bottom for the empty space.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `Scheme.proEtaleObjectInverseImageRestriction` supplies the abelian-sheaf restriction
  comparison without any monomorphism or finite-type restriction on the site object.

All already-stated proof-dependency modules are directly imported (without `public` unless
also a statement dependency). Mathlib matches use their named Mathlib modules. The upstream
finite-derived-sections module is resolved from its closed slopmaster2 audit because the
short attached `lean` record has no `module`. `sk-lem-integral-models` has no Lean statement
or closed upstream audit yet, so there is no module to import for that future proof input.
It is cited in the proof docstring and is not a prerequisite for typing this statement.

Searches for an existing statement (all via the prescribed msearch wrapper for NY/item):

- LeanSearch: `Pro-etale cohomology of integral lisse lattices under proper morphisms vanishes above 2d+1`.
  Eight hits, including `AlgebraicGeometry.IsProper.toLocallyOfFiniteType`,
  `Algebra.FormallyEtale.subsingleton_h1Cotangent`, `Scheme.smallEtaleTopology` and
  `AlgebraicGeometry.IsProper`; no integral lattice cohomology bound.
- LeanFinder: `Pro-etale cohomology of locally closed extension of integral lisse lattice vanishes above twice geometric fibre dimension plus one`.
  Eight hits about etale loci/formal etaleness, including `Algebra.etaleLocus_eq_compl_support`,
  `Algebra.formallyEtale_iff` and `AlgebraicGeometry.IsEtale.of_comp`; none matches.
- Loogle: `properHeartBoundLattice, IsZero, topologicalKrullDim`.
  Zero hits; unknown identifier `properHeartBoundLattice`.
- Mathlib grep: `properHeartBoundLattice|[Ll]attice.*[Cc]ohomology|topologicalKrullDim`.
  Twelve hits on topological Krull dimension and its applications, no lattice bound.
- Upstream and project `rg`: `heartBound|HeartBound|proper.*[Ll]attice|proper-heart-bound-lattice`,
  and `properHeartBoundLattice|lattice.*[Vv]anish|[Ll]attice.*2d|lattice.*2 \*`.
  Upstream gives no exact statement. Project has the torsion bound, the rational-coefficient
  consequence, and the ind-constructible heart bound. They concern different coefficients
  or direct images, so do not already state integral-lattice cohomology vanishing.
- `rg` of the exact node id in upstream `WeilConjectures`: no matches. No existing exact
  declaration was found. New declaration name checked against upstream, Mathlib and Sheaf.

Edge cases checked before writing and again on the signature:

- `d < 0` forces every geometric fibre empty, hence X empty; all integer q satisfying the
  strict bound remain allowed, including possibly nonpositive q. There is no artificial
  hypothesis `0 ≤ d`.
- `d = 0` gives exactly q > 1, not q > 0; `q = 2d+1` is excluded.
- The zero lattice is allowed by `Mod.IsFree` at rank zero.
- Empty X, S, Y or V are not excluded. Covers and the canonical functors handle them.
- Neither V nor X_V is assumed Noetherian, quasi-compact over the field, or finite type.
- Uniformizer choice does not enter the conclusion. Coefficients keep their continuous
  integral topology throughout. An identity immersion and an empty stratum are allowed.
- One explicit universe u covers schemes, k and E, as in the exact torsion interface; the
  small site retains its object universe u+1, morphism universe u and coefficient Ab u+1.
  No equality of site object and morphism universes or arbitrary map is introduced.

No STATEMENT-DISPUTED flag and no correction to the node are needed.

## Second reading by NY

This is the dispatch worker's second pass with the node and final signature open.
The dispatch instruction prohibits starting another agent; independent mathematical review
is left to the maintainer, as the brief states. This section does not claim an independent
reader performed this pass.

I compared the prime and extension binders, positive-characteristic/non-ell conditions,
all three finite-type separated schemes, the proper k-morphism, the signed geometric-fibre
bound, the affine weakly contractible site object, the open/closed factorization and its
k-linearity, the pulled-back integral module and local finite freeness, and the entire
cohomology expression against each clause of the node. The dependency's torsion quotient
is deliberately absent from the resulting cohomology: the sheaf used here is a_!L itself.
The strict inequality has the extra +1, and d remains signed. The underlying-sheaf inverse
image is the canonical restriction, justified by the already recorded general comparison,
not an assumption of a chosen transport. S's finite-type k-setting is explicit; neither V
nor the fibre product inherits such a requirement. No mismatch requiring a statement change
was found. This reading also checked that the full proof plan follows the seven updated
DAG steps and that no natural compatibility of individually chosen reductions is assumed.

Validation: `scompile.py NY det-proper-heart-bound-lattice` compiled the delivered file
cleanly in both sandbox (3.8 s) and library placement (9.8 s); no warnings or errors.
The required `deliver2.py ... --no-push` passed preflight and per-file compilation,
printing `OK (dry run)` for commit f4c53750e6. A local read-only comparison confirms
that only the node field `lean` changed, its signature matches the source verbatim,
there is exactly one theorem proof `sorry`, and all Lean lines are at most 100 characters.
