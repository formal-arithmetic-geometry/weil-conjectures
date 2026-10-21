## Worker report

The module `Sheaf.Paper.WeilGenericLissity` states
`WeilConjectures.weil_exists_dense_open_lisse`, with its sole theorem proof `sorry`.
The model-open helpers have explicit data; their finite-type instances use existing
Mathlib constructions. No statement correction, dependency repair, or new node is needed.
The item gains two already-landed statement dependencies, as authorized by brief-stage2 §5:
`def-a1-common-stage-lisse-lattice` and `def-zl-weil-ind-sheaf-category`.

Clause-by-clause correspondence:

- Finite field, cardinality q, fixed algebraic closure, and characteristic p:
  `D : FiniteFieldDatum.{u}` from `Sheaf.Paper.FiniteFieldFiber`.
- Prime ell different from the characteristic: `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- Algebraic closure of Q_l: `Ω : Type v`, `Field Ω`, `Algebra (Padic l) Ω`,
  `IsAlgClosure (Padic l) Ω`. Universes u and v remain independent.
- Scheme over the finite field: `X₀ : Over (Spec (.of D.k₀))`.
  Its finite-type structure map is `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`.
  Separatedness and reducedness are `[IsSeparated X₀.hom] [IsReduced X₀.left]`.
- X is exactly `(D.geometricFiber X₀).left`, the fixed chosen base change.
- The constructible Qbar_l-Weil sheaf, including its geometric Galois Frobenius
  isomorphism, is `F : sfCommonStageWeilSheaf D l hl X₀ Ω` from the recorded
  `Sheaf.Paper.SfWeilSheafComplex`. This is the full subcategory of fixed pairs
  in the actual common-stage category with the underlying heart property.
- The open subscheme is `U₀ : X₀.left.Opens`; density is `Dense (U₀ : Set X₀.left)`.
  `zlGenericOpenModel D X₀ U₀` is literally `Over.mk (U₀.ι ≫ X₀.hom)`.
  `zlGenericOpenInclusion` is literally `Over.homMk U₀.ι`.
  Thus its geometric fibre is U₀ times k over k₀, with the actual base-change inclusion.
- The restriction is `((zlWeilPull D l hl Ω (zlGenericOpenInclusion D X₀ U₀)).obj F)`.
  This is itself an object of `sfCommonStageWeilSheaf` on U₀, rather than an unrelated
  existential Weil structure. In `Sheaf.Paper.WeilIndSheafCategory`, `zlWeilPull`
  is the restriction of `IsoAlgebra.mapOfNatIso (zlFrobeniusSquare ...)` to the heart.
  Its carrier is actual common-stage derived pullback and its structure is the
  composition of the normalized Frobenius/pullback square with pulled-back theta.
  `zlFrobeniusSquare` uses the recorded integral composition on finite representatives
  and geometric Galois Frobenius naturality. This renders the final Weil clause.
- Adic lissity is `HasCommonStageLisseLattice l Ω ... restriction.obj.carrier`, from
  `Sheaf.Paper.CommonStageLisse`, declaration `WeilConjectures.HasCommonStageLisseLattice`.
  It retains a finite-stage finite locally free completed integral coefficient module
  N, its degree-zero integral realization M, and the actual common-stage isomorphism
  after rationalization. This is the existing completed presentation of the recorded
  Weil II inverse-system convention, not a new locally constant rational sheaf predicate.
- Empty model: `(IsEmpty X₀.left → U₀ = ⊤)` explicitly enforces U₀=X₀ in that case.

Original statement dependencies were read, including their full signatures and docstrings:
`FiniteFieldDatum`, `sfCommonStageWeilSheaf`, `sfCommonStageWeilFrobeniusPullback`,
`sfWeilPrimeInvertible`, and `Scheme.LisseIntegralSheafOfUniverses` with
`IsLisseIntegralDiagramOfUniverses` in `Sheaf.Paper.LisseIntegralSmallCoefficients`.
Reducedness uses `AlgebraicGeometry.IsReduced` in Mathlib.AlgebraicGeometry.Properties.
The scheme-conventions dependency fixes no new notion and has a convention-only record;
its meanings are the existing Mathlib LocallyOfFiniteType, QuasiCompact, IsSeparated,
Scheme.Opens, and their canonical open inclusions. All recorded proof-dependency modules
are imported for stage 3; the docstring gives all six proof steps and their arguments.

Edge cases checked: empty model and empty geometric fibre; zero sheaf/rank zero;
disconnected or reducible schemes with varying ranks; identity/top open; arbitrary fixed
algebraic closures and independent site/coefficient universes. No nonempty, irreducible,
smooth, geometrically connected, Frobenius-stable lattice, or constant-rank hypothesis is
imposed. Quasi-compactness of each model open is derived using noetherianity of X₀ from
finite type over a field, not added as a hypothesis.

Searches actually run:

- msearch leanfinder: “A constructible adic Weil sheaf is lisse on the base change of
  a dense open of its finite field model”. Eight hits concern condensed modules,
  sheafification, and affine limits; no exact theorem.
- msearch loogle: `"IsLisse", "WeilSheaf"`. Zero hits.
- msearch grep: `IsAdicLisse|WeilSheaf|generic.*liss`. Zero Mathlib hits.
- msearch leansearch: “A constructible rational adic Weil sheaf has a dense open lisse
  restriction defined over the finite field”. Eight hits concern scheme restrictions,
  rational partial maps, constructible subsets and condensed sheaves; no exact theorem.
- rg in the prescribed project trees for generic lissity and the node id located
  `WeilConjectures.WeilSheaf.LisseLocus`. Read the complete existing generic-lissity
  theorem `AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar` and its proof:
  it uses upstream `WeilSheaf k₀ l X` and the pro-etale AdicSheaf category, not the
  recorded common-stage constructible-heart pair category; it is not an exact match.
- Further rg searches in Sheaf and the DAG located the already-landed
  `HasCommonStageLisseLattice`, `IsCommonStageLisse`, and `zlWeilPull`. Read both
  lissity definitions and selected the integral-lattice convention the node requires.
  Read `def-a1-common-stage-lisse-lattice` and `def-zl-weil-ind-sheaf-category` before
  adding their ids. No missing independent notion was introduced.

The current blueprint stratification proof, paragraphs 1 and 4, was read in full.
There is no STATEMENT-DISPUTED finding. The original natural-language statement is unchanged.

Validation: scompile.py compiled the first statement module cleanly (sandbox 3.6 s,
library 4.0 s). All final imports and the delivery are checked again by the prescribed
scompile.py/deliver2.py wrappers. No library file, launcher script, or shared git state
was edited directly.

## Second reading by N0

This is the author's explicit clause audit, not a claim of an independent worker review;
the dispatcher forbids starting other agents and the maintainer independently reviews
this delivery. Re-read the node, its dependencies, and the module together. Confirmed
all field/prime/scheme assumptions, the actual common-stage heart carrier, the dense
finite-field open, integral adic lissity of its canonical Weil restriction, and the
specified empty-model choice. In particular, the original upstream theorem cannot be
recorded as existing because its Weil category differs. No statement mismatch or
further correction was found. The final theorem has only sorry; helpers contain real
data and inherited instances, and no source hypothesis is added.
