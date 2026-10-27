## Worker report

Stated `AlgebraicGeometry.principalUnion_restriction_kernel_localization` in
`Sheaf.AlgebraicGeometry.PrincipalUnionRestrictionKernelLocalization`.
This is the only declaration, with proof `sorry`; there are no new definitions.
The original node is preserved, adding only its `lean` record.

Sources read: Stacks Project, `morphisms.tex`, Tag 056C,
`example-scheme-theoretic-closure` (the displayed ideal
`Ker(A → ∏ A_fi)`); `schemes.tex`, Tag 01HV, `lemma-spec-sheaves`,
particularly (1), (3), (5). These give the same ring, finite family, kernel and
restriction-induced section identifications as the node. The four-step proof
in the theorem docstring reproduces the accepted DAG proof, including the
common-exponent argument and empty-cover convention.

Hypotheses and clauses, matched against the signature:

| Node | Lean rendering |
| --- | --- |
| Any commutative ring A | `(A : Type u) [CommRing A]`, explicit arbitrary universe `u` |
| X = Spec A | `Spec (CommRingCat.of A)` |
| n ≥ 0, f_1,...,f_n | `(n : ℕ) (f : Fin n → A)`; zero-based indexing merely reindexes the finite family |
| A_h = A[1/h] | `Localization.Away h` |
| D(h) = primes not containing h | `PrimeSpectrum.basicOpen h` |
| U = union of the D(f_i) | `⨆ i : Fin n, PrimeSpectrum.basicOpen (f i)` |
| K = elements zero in every A_fi | `(∀ i : Fin n, algebraMap A (Localization.Away (f i)) a = 0)` |
| Every g in A | `(g : A)` |
| Section identification on D(g), induced by global restriction | `IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) ((Spec.structureSheaf A).obj.obj (op (PrimeSpectrum.basicOpen g)))` |
| Restriction D(g) → D(g) ∩ U | `(Spec (CommRingCat.of A)).presheaf.map (homOfLE (inf_le_left : D(g) ⊓ U ≤ D(g))).op`, with D(g) and U expanded in the file |
| Kernel, considered as a subset of A_g | Set comprehension over `z : Localization.Away g` whose identified section restricts to `0` |
| Exactly the fractions a/g^r for a in K, r ≥ 0 | Set comprehension with `∃ a : A`, the displayed condition defining K, and `∃ r : ℕ, z = Localization.mk (S := Submonoid.powers g) a ⟨g ^ r, ⟨r, rfl⟩⟩` |
| Equality of those subsets | Literal equality of the two set comprehensions |

The section ring in the isomorphism is definitionally the structure-sheaf
section ring of the displayed scheme on D(g), as confirmed by compilation.
Its existing `StructureSheaf.openAlgebra` is the restriction-compatible
A-algebra: `StructureSheaf.algebraMap_self_map` states compatibility with
restriction; `StructureSheaf.globalSectionsIso` identifies the global map
with A. `StructureSheaf.IsLocalization.to_basicOpen` supplies its canonical
localization structure. Thus the algebra equivalence is exactly the
restriction-induced identification of dependency clause (b), and is not a
chosen arbitrary ring isomorphism. Using the structure-sheaf expression rather
than the scheme notation makes this existing algebra instance visible to Lean.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` (and its recorded `Spec.map`, read).
- `def-weil-ring-localization-away`:
  `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`;
  ring structures and `IsLocalization.Away` from
  `Mathlib.RingTheory.Localization.Away.Basic`. Fractions use the existing
  `Localization.mk` with explicit submonoid, not a new fraction definition.
- `lem-weil-pbc-affine-open-section-vanishing-prime`: the recorded Mathlib
  interface was read in full: `Scheme.evaluation_eq_zero_iff_notMem_basicOpen`,
  `IsAffineOpen.fromSpec_preimage_basicOpen`, `IsAffineOpen.fromSpec_primeIdealOf`,
  `PrimeSpectrum.mem_basicOpen`, `IsAffineOpen.basicOpen`, and
  `IsAffineOpen.isLocalization_basicOpen`. Here the only required clause is
  (b), specialized to Spec A; its direct existing specialization is
  `StructureSheaf.IsLocalization.to_basicOpen`. `AffineScheme` is a public
  statement import; `IsLocalization.algEquiv` is publicly imported from
  `Mathlib.RingTheory.Localization.Basic`.
- Proof dependency `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its module and docstring
  were read and it is a plain proof import.
- Proof dependency `lem-weil-pbc-basic-open-function`: its recorded
  `Scheme.basicOpen`, `Scheme.mem_basicOpen`, `Scheme.basicOpen_le`,
  `Scheme.evaluation_ne_zero_iff_mem_basicOpen`, and
  `RingedSpace.isUnit_res_basicOpen` were read. The additional ResidueField
  module is a plain proof import; the other declarations are already supplied
  by the statement imports.

No dependency interface needs repair: the item only uses the already available
principal-open localization clause, not a new package of all equivalent
characterizations.

Edge cases checked mathematically before and after writing:

- `n = 0`: the supremum is the empty open, the condition defining K is
  vacuous, and every localized element is a fraction; both sides are all A_g.
- The zero ring is permitted by `[CommRing A]`; all section and localization
  rings are zero and the assertion remains valid.
- `g = 0` or nilpotent g: D(g) is empty and A_g is zero, with no nonzero or
  nonnilpotence condition in the signature.
- All f_i nilpotent: U is empty, all localizations A_fi are zero, and K = A.
- Some f_i a unit: U is all of X and K = 0, so the identity restriction has
  zero kernel. Unit g gives the global restriction-kernel calculation.
- Zero divisors and nilpotents are retained. In k[ε]/(ε²), f = ε makes
  the open empty. In k[x,y]/(xy), f = x and g = y give K = (y), whose image
  becomes the entire ring A_y because y is inverted. The common exponent
  argument handles this case without assuming reducedness or injective
  localization.
- Exponent `r = 0` and repeated f_i are admitted. There is no additional
  finiteness, domain, Noetherian, or nonempty-cover hypothesis.

Searches for an existing statement (2026-10-24):

- `msearch.py`, LeanFinder: “Kernel of restriction on a finite union of
  principal opens in an affine spectrum consists of fractions whose numerator
  vanishes in every localization”. Eight results, including
  `StructureSheaf.normalize_finite_fraction_representation`,
  `Scheme.ker_morphismRestrict_ideal`, and ideal-sheaf gluing/kernel lemmas.
  These do not state the displayed fraction-set equality.
- `msearch.py`, Loogle: `IsLocalization.algEquiv, RingHom.ker`: zero hits.
  The `algEquiv` definition was located and read directly in Mathlib.
- `msearch.py`, LeanSearch: “ideal of functions vanishing on finite union of
  principal open subsets localization commutes with restriction kernel”.
  Eight results, including `PrimeSpectrum.vanishingIdeal`,
  `Scheme.IdealSheafData.map_ideal'`, `Scheme.ker_morphismRestrict_ideal`,
  `Γ_restrict_isLocalization`, and the open-cover kernel infimum.
  None states this fraction-set equality. In particular the topological
  vanishing ideal is a different notion over nonreduced rings.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `ker_apply|ker_morphismRestrict_ideal|map_ideal_basicOpen|isLocalization_basicOpen`:
  25 hits. Read `Scheme.Hom.ker_apply` in IdealSheaf/Basic: it computes
  schematic-image ideals on affine opens, rather than the node's explicit
  subset of A_g. `IsAffineOpen.isLocalization_basicOpen` supplies an ingredient.
- `rg` in both project trees for
  `principalUnion|principal_union|restriction_kernel|restrictionKernel|kernel_localization`
  found unrelated punctured-neighbourhood kernels, formal-modules restriction
  factorization and a principal-union intersection helper. No exact statement.
  Searching the item's id in WeilConjectures found no declaration.
- The proposed full declaration name was searched in Mathlib and both project
  trees; no collision. `dag/lean_names_upstream.json` was searched for
  `principal.*kernel|kernel.*principal|principal.*restriction`, with no match.

No new nodes, dependency modules, statement correction, or disputed statement.

Validation: `scompile.py` checked the module on the published server build in
both sandbox and library module modes. The final run passed both checks with
no errors or unexpected warnings. An initial elaboration failure was repaired
by exposing the existing structure-sheaf algebra instance and explicitly
specifying the denominator submonoid; the mathematical statement was unchanged.

## Second reading by Q17

Independent maintainer second reading (cc review service, 2026-10-24) of the
node against `Sheaf/AlgebraicGeometry/PrincipalUnionRestrictionKernelLocalization.lean`;
it replaces the worker's self-audit section (delivery-errors H11). Nothing in the
Lean or the records was changed.

Node clauses and their Lean rendering:

| Node clause | Lean | Verdict |
| --- | --- | --- |
| A commutative ring, no further hypotheses | `(A : Type u) [CommRing A]`, `u` arbitrary | exact |
| X = Spec A (def-weil-affine-spectrum) | `Spec (CommRingCat.of A)`; its presheaf on `PrimeSpectrum A` is `Spec.structureSheaf A` definitionally | exact |
| n ≥ 0, f_1..f_n ∈ A | `(n : ℕ) (f : Fin n → A)`; n = 0 allowed, repetitions allowed | exact (reindexing only) |
| A_h = A[1/h] (def-weil-ring-localization-away) | `Localization.Away h` | exact |
| D(h), U = ⋃ D(f_i) | `PrimeSpectrum.basicOpen h`, `⨆ i : Fin n, PrimeSpectrum.basicOpen (f i)` (⨆ of opens = union) | exact |
| K = {a : image in every A_{f_i} is 0} | `∀ i, algebraMap A (Localization.Away (f i)) a = 0` | exact |
| every g ∈ A | `(g : A)`, no unit/non-nilpotence hypothesis | exact |
| O_X(D(g)) ≅ A_g induced by restriction from O_X(X)=A (lem-weil-pbc-affine-open-section-vanishing-prime (b) on U = X) | `IsLocalization.algEquiv (powers g) (Localization.Away g) Γ(D(g))` using Mathlib's `StructureSheaf.openAlgebra` (algebra map = toOpen, equal to restriction of global sections by `algebraMap_self_map`/`globalSectionsIso`) and instance `StructureSheaf.IsLocalization.to_basicOpen` (StructureSheaf.lean:945–953) | exact; canonical A-algebra iso, not a chosen one |
| restriction O_X(D(g)) → O_X(D(g) ∩ U) | `presheaf.map (homOfLE inf_le_left).op` from `D(g)` to `D(g) ⊓ U` | exact, right direction |
| kernel as a subset of A_g | `{z | map (e z) = 0}` | exact |
| {a/g^r : a ∈ K, r ≥ 0} | `∃ a, K-condition ∧ ∃ r, z = Localization.mk a ⟨g^r, ⟨r, rfl⟩⟩` | exact |
| equality of subsets | `Set` equality | exact |

The `lean.statement` of the node copy is verbatim the signature in the file.
The module docstring and the theorem docstring give the source place (Tags
056C, 01HV) and `(blueprint: lem-trf-principal-union-restriction-kernel-localization)`;
the theorem docstring carries the node's four proof steps. Proof is `sorry`;
no definitions, so no hollow data. Imports: public Mathlib AffineScheme and
Localization.Basic for the statement; ResidueField and SiteCoveringAxioms are
proof-dependency imports.

Edge cases: n = 0 (U = ∅, both sides all of A_g); A = 0; g = 0 or nilpotent
(A_g = 0, D(g) = ∅); all f_i nilpotent (K = A); some f_i a unit (K = 0);
k[x,y]/(xy) with f = x, g = y (K = (y), image all of A_y; the kernel on
D(y)∩D(x) = ∅ is everything). All are covered by the unrestricted binders.
Universe: single `u`, no restriction.

Searches: the worker's records were re-read; Mathlib `StructureSheaf.lean`
(basic-open localization instances), `IdealSheaf/Basic.lean` (`Hom.ker_apply`,
`ker_morphismRestrict_ideal`) state different results; no declaration in the
live project tree with this name or content.

Mismatches found: none in the Lean or records. Only the report's second-reading
section was replaced.
