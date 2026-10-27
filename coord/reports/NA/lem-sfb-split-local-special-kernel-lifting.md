## Worker report

The item is stated by `AlgebraicGeometry.splitLocalSpecialKernelLifting` in
`Sheaf.AlgebraicGeometry.SplitLocalSpecialKernelLifting`. Its proof is `sorry`.
`Sheaf.AlgebraicGeometry.RingDiagonalizableGroup` supplies the explicit ring-based
Hopf-spectrum construction needed for its source and quotient inclusion. Both
modules compiled cleanly, individually and in dependency order through the prescribed
`scompile.py` against the live published library on 2026-10-24. No proofs or live
files were edited. No statement correction or disputed statement is needed.

The inherited BLOCKED ending concerned an unchanged stage-1 split. The current
stage-2 queue row is `lem-sfb-split-local-special-kernel-lifting 2 ... state`,
the item has no Lean record, and there is no released repair note or return entry.
The accepted split is preserved. This delivery changes only its `lean` and adds the
new definition dependency to `stmt_deps`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `(R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]` is the nonzero
  commutative Noetherian local ring. Mathlib `IsLocalRing` extends `Nontrivial R`,
  so nonzeroness is included. Its maximal ideal is `IsLocalRing.maximalIdeal R`.
- `IsLocalRing.ResidueField R` is exactly `R ⧸ IsLocalRing.maximalIdeal R` and
  `IsLocalRing.residue R` is the quotient homomorphism. Each `Over.pullback` is
  along `Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))`, hence the closed
  fibre over this residue field, with the specified canonical base map.
- `S` is `Spec (.of R)`, and `G : Over (Spec (.of R))` is an S-scheme.
  `[GrpObj G]` gives its multiplication, unit and inverse with the group diagrams;
  the generic category-theoretic structure requires no field hypothesis.
- `(r : ℕ)` includes r=0. `Fin r → ULift.{u} ℤ` is the standard lattice Z^r,
  transported by the canonical coordinatewise `ULift.down` additive equivalence.
  The lift only matches the fixed universe of schemes and coefficients; it
  changes neither subgroups nor group algebras up to their canonical isomorphisms.
- `ringDiagonalizableGroup R M` is literally `hopfSpec` applied to
  `CommHopfAlgCat.of R (AddMonoidAlgebra R M)`. Mathlib's Hopf structure has the
  displayed basis multiplication, coproduct, counit and antipode. Thus its value
  at the standard lattice is precisely the node's P=D_R(Z^r), with its specified
  group law. The new definition handles the initial D_R(M) convention for every
  finitely generated M (and does not unnecessarily require finite generation).
- `[IsSeparated G.hom]` is separatedness over S. Finite presentation in the
  recorded scheme conventions is exactly `[LocallyOfFinitePresentation G.hom]`,
  `[QuasiCompact G.hom]` and `[QuasiSeparated G.hom]`. No smoothness, affineness,
  flatness or commutativity condition is imposed on G.
- `(f : (ringDiagonalizableGroup R ...).X ⟶ G) [IsMonHom f]` is the S-group
  homomorphism u. The Over morphism is already an S-morphism, and `IsMonHom`
  expresses compatibility with its group structure, including the identity.
- `∃ L : AddSubgroup (Fin r → ULift.{u} ℤ)` is precisely the subgroup of Z^r.
  All its occurrences use this single L and its actual quotient group.
- `ringDiagonalizableGroupMap R (QuotientAddGroup.mk' L)` is j, with coordinates
  e_a ↦ e_[a]. Its `.hom.hom` is the underlying Over morphism and `.left` the
  underlying scheme morphism. It is a bundled group homomorphism, rather than
  an unspecified morphism or arbitrary choice of a subgroup model.
- The first conjunct `IsClosedImmersion ...left` is the asserted closed immersion.
- The second conjunct `IsPullback j_k p_k f_k e_k` is the equality of j_k with the
  scheme-theoretic kernel inclusion. All four arrows are obtained by the SAME
  `Over.pullback` functor: j, the structure map to the terminal S-scheme, f, and
  G's unit section. The top-right corner is the pullback of the terminal S-scheme,
  canonically Spec k; its comparison is the canonical terminal-object isomorphism.
  Consequently the square is exactly H_k = P_k ×_(G_k,e_k) Spec k, with the
  specified arrow to P_k. This retains the embedding and the nonreduced scheme
  structure, rather than merely an abstract isomorphism or equality on points.
- The last conjunct `j ≫ f = toUnit ... ≫ η[G]` is u∘j=e_G∘p_H, the required
  identity-valued homomorphism over R itself.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg` (all ideals finitely generated).
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField` and `Scheme.Hom.residueFieldMap`. The former is explicitly
  the local-ring residue field of the stalk. Here the ring R is already local,
  so the exact constituent `IsLocalRing.ResidueField` and its quotient map
  `IsLocalRing.residue` from `Mathlib.RingTheory.LocalRing.ResidueField.Defs` apply
  directly; no second residue-field definition or record repair is needed.
- `def-weil-affine-spectrum` and `def-pc-scheme`:
  `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`, `Scheme`, and scheme Hom.
- `def-sc-gm-ga`: `Sheaf.AlgebraicGeometry.StandardGroupSchemes`,
  `StandardGroupSchemes.multiplicative`, `multiplicativeGroup`, `affine`, `map`,
  `multiplication` and `identitySection` were read with their signatures/docstrings.
  These require `[Field k]`; the item itself explicitly defines P as D_R(Z^r).
  The new ring-based construction supplies that expression without imposing a
  field hypothesis on R or redefining the recorded field-based G_m declaration.
- `def-weil-pbc-scheme-conventions` is a convention-only record; its actual
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` and `IsSeparated`
  predicates are used directly, according to the record's instructions.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  whose module docstring and `baseChange_morphism_projections` explain and use the
  same `Over.pullback` construction (object pullback, morphism universal lift).
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`.
- The new dependency's exact definitions are
  `AlgebraicGeometry.ringDiagonalizableGroup` and `ringDiagonalizableGroupMap`
  in `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`. They use Mathlib
  `hopfSpec`, `CommHopfAlgCat.of`, `CommHopfAlgCat.ofHom`, and
  `AddMonoidAlgebra.mapDomainBialgHom`, without postponed data or extra axioms.

The proof docstring carries all five accepted proof steps. Proof dependencies
with usable modules are imported: Proper (separated diagonal), ClosedImmersion
(base-change stability), Pullbacks via the base-change module (affine product),
Group.Affine via the new definition (coordinate Hopf algebra), Coalgebra.GroupLike
(group-like independence), and Filtration (Krull intersection).
`lem-sfb-diagonalizable-nilpotent-triviality` has no Lean record or Mathlib match;
it is solely a proof dependency and cannot yet supply an import. The statement
needs none of its declarations, so no premature theorem or dependency cycle is
introduced in this stage-2 delivery.

Edge cases checked against the node and source:

- r=0 gives the trivial torus, with its unique character subgroup and quotient.
- R a field gives the original special fibre; local Artinian and nonreduced R
  remain allowed. Completeness, Henselianity and a domain condition are absent.
- L=0 gives the whole torus killed by f; L=Z^r gives the identity subgroup.
- Characteristic p and a quotient lattice with p-torsion yield μ_p and other
  nonreduced diagonalizable kernels. The cartesian square tests schemes, not
  geometric points. No algebraic-closure or reducedness hypothesis appears.
- Arbitrary separated, finitely presented group targets are permitted.
- The zero ring is excluded by `IsLocalRing`, as the node requires.

Searches (all before choosing the construction; `msearch.py` logged its own results):

- LeanFinder: "The special fibre kernel of a split torus homomorphism over a
  Noetherian local ring lifts to a diagonalizable subgroup scheme". Eight hits
  concern Selmer/valuation kernels and algebra lifts; no scheme-theoretic lifting.
- LeanSearch: "diagonalizable group scheme over an arbitrary commutative ring
  spectrum of the group algebra". Eight hits concern `Rep.diagonal`, affine
  spectra and Maschke; none supplies the specified diagonalizable group.
- LeanFinder: "diagonalizable group scheme spectrum of the additive group
  algebra over a commutative ring". Eight hits are ordinary affine space,
  Spec and diagonal morphisms; no named diagonalizable-ring construction.
- Loogle: `"hopfSpec"`. Five hits include `AlgebraicGeometry.hopfSpec`, its
  fullness/faithfulness and essential-image statements. Its exact signature is
  over `R : CommRingCat`; it is the general functor reused here.
- Mathlib grep via msearch: `diagonali[sz]able|torus.*kernel|kernel.*torus`,
  subdirectory AlgebraicGeometry: zero hits.
- Project `rg -l 'diagonalizableGroup|ringDiagonalizable|relativeDiagonalizable'`
  in `lean/Sheaf` and `lean/WeilConjectures`: only the field-based DiagonalizableGroup
  module and its field-based consumers. Its exact signature has `[Field F]`.
  The original item id has no match in `lean/WeilConjectures`.
- DAG grep of definition nodes for diagonalizable over a ring found only
  `def-sfb-diagonalizable-group` (explicitly a field), and
  `def-sfb-finite-diagonalizable-group-scheme` (finite groups over a field).
  `python3 tools/blueprint_refs.py search diagonalizable` returned zero blueprint
  nodes; `ancestor` returned None, as the item's accepted provenance says.
- New declaration names were checked against Mathlib, the upstream declaration
  index and both source roots: no prior definitions were found.

Source verification: read Conrad's author PDF at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Appendix B.1 on
printed p.280 and Corollary B.2.7 on printed p.287. The former gives D_S(M),
its contravariant maps and quotient subgroup description; the latter explicitly
permits an arbitrary target group scheme. The item combines those with the
accepted coefficientwise Krull-intersection proof, and is not a blueprint unit's
own statement. No source-based correction is needed.

## New nodes

`def-sfb-ring-diagonalizable-group` defines D_R(M) and D_R(α), including the
canonical quotient-lattice inclusion. Its source is Conrad Appendix B.1, p.280.
It is required because the existing `def-sfb-diagonalizable-group` and the recorded
G_m declarations restrict coefficients to a field, while this item uses a
Noetherian local ring. The searches above are recorded verbatim as logged in the
new node's `mathlib_searches`; no existing arbitrary-ring diagonalizable node was
found. Its two abbreviations contain the full canonical Hopf-spectrum construction
from Mathlib, not a choice or missing data. The character group and R share a
universe, and the finitely generated lattice in the item is explicitly lifted to
that universe. The item cites this new definition directly.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
