## Worker report

The delivery states `AlgebraicGeometry.affine_perfect_open_represent_cohomology` in
`Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology`. Its proof is `sorry`.
It adds the canonical Koszul-tail construction in
`Sheaf.AlgebraicGeometry.KoszulOpenSystem`, with no postponed data. The proof obligations
needed to construct complexes and functors are named theorems with `sorry` and complete
proof explanations, carried by the definition node `def-sc-koszul-open-system`.

Clause-by-clause rendering:

- The commutative ring is `(A : Type uMain) [CommRing A]`. The affine scheme is
  Mathlib's `Spec (.of A)`, rather than an unconstrained scheme with an unused equality.
- The finite sequence is `(r : ℕ) (f : Fin r → A)`. `koszulOpen A r f` is exactly
  `⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)`.
- `E : schemeDerivedQCohCategory (Spec (.of A))` imposes precisely quasi-coherent
  cohomology, without a boundedness hypothesis. `E.1` is its underlying derived object.
- Source exponent `e ≥ 1` is represented by index `e : ℕ` and exponent `e+1`.
  `koszulOpenTail` has term `⋀[A]^(n+1) (Fin r →₀ A)` in chain degree `n`, and
  differential minus the existing Koszul boundary. Extension by
  `ComplexShape.embeddingDownNat` gives degree `-n`, and zero in positive degrees.
  Thus its degree `i ≤ 0` term is exactly `K^{i-1}`.
- `koszulOpenTilde` transports Mathlib's existing associated-sheaf functor to the
  project's shared `SheafOfModules` category, with identical objects and maps.
  `koszulOpenObject` applies the existing localization `DerivedCategory.Q` to this
  termwise associated complex. `koszulOpenKoszulObject` does the same for the full
  existing Koszul complex.
- `koszulOpenStructure` is the termwise associated single complex `A[0]`, hence a
  representative of `O_X` in the same category. The augmentation is the existing
  Koszul boundary `K_1 → K_0`, followed by Mathlib's degree-zero exterior-power
  identification with `A`. It is transported to `koszulOpenUnit`.
- `koszulOpenKoszulUnit` is the canonical inclusion `A → K_0`, transported in the
  same way. The first conclusion supplies a connecting arrow `δ` making these two
  specified arrows and specified objects a distinguished triangle.
- `koszulOpenMap a b h` is the exterior power of the diagonal map with coefficients
  `f_i^(b-a)`, extended, sheafified, and localized. For successive source exponents
  this multiplies a wedge by the product of its `f_i`. The second substantive
  clause states compatibility with the augmentations for every `a ≤ b`.
- `∀ e, Scheme.IsPerfect … (koszulOpenObject … e)` is precisely perfectness of each tail.
- The existential `v e` and its two inverse identities state that each augmentation
  restricted to the actual `koszulOpen` is an isomorphism. Restriction everywhere is
  the shared `(SheafOfModules.overFunctor … U).mapDerivedCategory`.
- `koszulOpenHomDiagram` is the directed diagram `e ↦ Hom(I_{e+1},E)` with transition
  by precomposition with the actual power comparison. The cocone `ι` has target
  `Hom(O_U,E|_U)`, explicitly the degree-zero cohomology identification used in
  the source and node; its formula is `ι.app e φ = v e ≫ restriction φ`.
  `Nonempty (IsColimit (Cocone.mk _ ι))` says that this canonical comparison
  realizes the filtered colimit. Equivalently, the induced canonical map from any
  chosen colimit is bijective (an additive-group isomorphism, since the leg maps are
  additive). This is the requested comparison isomorphism, using its universal property.
- The derived-category instance binders provide the chosen localizations at `X`
  and its opens, as required by the recorded derived category and perfectness definitions.

Dependency declarations read and used: `AlgebraicGeometry.Scheme` and its morphisms
(Mathlib.AlgebraicGeometry.Scheme); `AlgebraicGeometry.schemeDerivedCategory` and
`schemeDerivedQCohCategory` (Sheaf.AlgebraicGeometry.DerivedCategory);
`AlgebraicGeometry.Scheme.IsPerfect` (Sheaf.AlgebraicGeometry.PerfectComplex);
`ExteriorAlgebra.koszulComplex`, `koszulBoundary`, and `koszulBoundary_comp`
(Sheaf.Paper.KoszulComplex). The new definition node imports these existing notions,
not a second Koszul differential. Mathlib's `tilde.functor`, `exteriorPower.map`,
`exteriorPower.zeroEquiv`, complex extension, single-complex morphism equivalences,
and the colimit cocone notion are used directly. All signatures and docstrings of
these dependencies were inspected. There are no dependency replacement modules.

Edge cases: `r=0` is allowed; the positive exterior powers vanish, so the tails are
zero and `U=⊥`. Both degree-zero Hom groups and their colimit are zero. For `E=0`
both sides likewise vanish. A zero ring and all-zero `f_i` are allowed; the open is
empty and the conclusion remains consistent. For an invertible `f_i` the union is
all of `Spec A` and the tail augmentation is a quasi-isomorphism. No regular-sequence,
Noetherian, characteristic, boundedness, or nonemptiness assumption is added.

Sources were read at https://stacks.math.columbia.edu/tag/08CX,
https://stacks.math.columbia.edu/tag/08DC, and
https://stacks.math.columbia.edu/tag/08DD because the local perfect.tex packet is absent.
The negative tail differential, augmentation formula, comparison multipliers, and
unbounded quasi-coherent hypothesis agree with these sources. No node statement
correction is required.

Searches performed with msearch.py:

- LeanFinder: "Koszul perfect complexes represent cohomology on a finite union of
  principal opens": eight generic K-projective/derived cohomological bound hits,
  no representation proposition.
- Loogle: "KoszulComplex, DerivedCategory": zero hits, unknown identifier KoszulComplex.
- Grep: "koszul|Koszul" in Mathlib/Algebra: only the local-cohomology TODO/docstring hit.
- LeanSearch: "truncated Koszul complex inverse system powers": unavailable,
  Internal Server Error; no mathematical verdict inferred from this failure.
- LeanFinder: "Koszul complex truncation I with negative differential and power
  comparison maps": generic truncation and augmentation operations, no constructed
  negative-tail power system. Their types were checked in source.
- Grep: "koszulOpen|Koszul.*[Ss]ystem|[Tt]runcated.*Koszul" in Mathlib: zero hits.
- rg of WeilConjectures and lean/Sheaf: the full project Koszul complex and generic
  tilde construction exist and are used; no truncated power system or representation
  proposition. The item id itself has no source declaration.
- blueprint_refs.py search Koszul and rg of DAG nodes: intrinsic completion nodes
  concern full Koszul complexes and derived limits; comparison statement nodes
  mention the tail but do not define it. No existing definition node for this system.

An initial scratch statement with unconstrained objects was rejected by the author
and replaced completely. The present statement has no `True` placeholders,
unconstrained comparison map, or global-invertibility assertion.

## New nodes

`def-sc-koszul-open-system` supplies the otherwise missing explicit negative Koszul-tail
power system of Tags 08CX/08DC, the augmentation, full Koszul object and inclusion,
and its derived Hom diagram. It is built from the existing full Koszul complex and
Mathlib tilde, exterior powers, and complex localization. Searches above distinguish
it from the existing full Koszul complex and intrinsic-completion definitions.
Its named proof obligations are square-zero, augmentation-annihilation of boundaries,
commutation of power comparisons with differentials, tilde additivity, the identity
and composition laws of comparisons, and the Hom functor laws. These have docstrings
with complete natural-language proofs; their proofs are postponed, their data are not.

## Earlier second reading (a previous round; superseded)

Pending the independent second worker explicitly assigned after this author by the
user's brief. No independent second reading has been performed or claimed here.
This section is reserved for that worker's actual findings before delivery.

## Second reading by M1

Independent second reader; I opened the item node, both delivery modules, the four
recorded dependency nodes and their declaration sources. I read the full section
https://stacks.math.columbia.edu/tag/08CX and Tags 08DC and 08DD, including Situation
36.9.1. The local perfect.tex packet is absent. The source assumes only a
commutative ring and a finite sequence; its proposition permits unbounded E.

Objects, hypotheses and conclusions, matched individually:

1. A commutative ring A: `(A : Type uMain) [CommRing A]`; PASS, no domain,
   field, Noetherian, regularity or characteristic assumption.
2. X = Spec A: every category and restriction uses `Spec (.of A)`; PASS.
   I opened Mathlib Scheme and Spec: these are schemes and the ring spectrum.
3. A finite sequence f_1,...,f_r: `(r : ℕ) (f : Fin r → A)`; PASS including r=0.
4. U = union of D(f_i): `koszulOpen A r f`, defined by the indexed supremum of
   `PrimeSpectrum.basicOpen (f i)`; PASS, the actual specified open.
5. E in D_QCoh(O_X): `E : schemeDerivedQCohCategory (Spec (.of A))`; PASS.
   `schemeDerivedQCohProperty` quantifies quasicoherence over every integer
   cohomology degree; no boundedness is imposed. E.1 is the ambient derived object.
6. Positive exponents e: Lean indexes all naturals by exponent e+1; PASS, a
   reindexing bijection with all positive integers, including source exponent 1.
7. Full K_e and tail I_e: `koszulOpenKoszulObject` uses the recorded
   `ExteriorAlgebra.koszulComplex`; `koszulOpenTail` has exterior degree n+1
   at chain degree n with the negative recorded `koszulBoundary`.
   `embeddingDownNat` sends n to -n and extension sets positive degrees to zero.
   `koszulOpenTilde` uses Mathlib tilde objects/maps and transports their category
   structure to the shared SheafOfModules category. Localization is DerivedCategory.Q.
   PASS: exactly I^i = K^{i-1} for i<=0, zero otherwise, not a private Koszul complex.
8. Structure module and canonical arrows: `koszulOpenStructure` is tilde of A[0];
   `koszulOpenUnit` is boundary K_1 -> K_0 followed by `exteriorPower.zeroEquiv`;
   `koszulOpenKoszulUnit` is inclusion A -> K_0 via its inverse. The first conjunct
   existentially supplies the third arrow making `Triangle.mk` distinguished.
   PASS: its first two arrows and all objects are fixed, not arbitrary witnesses.
9. Canonical inverse system and compatibility: `koszulOpenMap a b h` is exterior
   power of the diagonal f_i^(b-a), sheafified and localized; the named map laws
   supply identities/composition. The third conjunct asserts map followed by u_a
   equals u_b for every a<=b. PASS, including identity and successive transitions.
10. Every I_e perfect: the second conjunct is `∀ e, Scheme.IsPerfect ...`; PASS.
    I opened its shared local strictly-perfect definition; the derived-category
    instance binders match its required choices, not extra geometric hypotheses.
11. Every restricted u_e invertible: existential v is a family of actual restricted
    arrows and both compositions are identity. PASS, equivalent to IsIso without
    adding a coherent choice assumption, and restriction uses shared overFunctor.
12. Canonical comparison into H^0(U,E|_U): the Hom diagram transitions are
    precomposition with the fixed power maps; the target is exactly restricted
    Hom(O_X,E), the Hom(O_U,E|_U) identification expressly allowed by the node
    and Tag 08DC. The formula `ι.app e φ = v e ≫ restriction.map φ` fixes every
    cocone leg. `Nonempty (IsColimit (Cocone.mk _ ι))` says precisely that this
    canonical comparison is bijective, by the universal property of the directed
    colimit. All legs are additive, so this also gives the asserted group
    isomorphism. PASS; no unconstrained comparison or weakened surjectivity claim.

Edge cases: empty Fin 0 makes U empty and every tail zero, while K=A[0],
so the triangle and zero Hom comparison agree. E=0 gives zero Hom sets/groups.
The zero ring gives an empty spectrum and is allowed. All f_i=0 also gives
empty U; positive-degree tail transition components eventually vanish, consistent
with the zero colimit. A unit among the f_i gives U=X and contractible full K.
Exponent index 0 means source exponent 1, never exponent zero. All characteristics
and arbitrary ring universes are allowed. uMain and wMain are bound; wMain is the
shared derived Hom universe, not a smaller test-object universe. No free variable,
extra finiteness condition or nonempty-open condition appears.

Independent searches (different phrases from the author's):

- LeanFinder: "derived sections on an open subset as direct limit of morphisms
  from perfect Koszul complexes": eight generic sheaf/generator/tilde hits;
  no Koszul representation theorem or augmented power system.
- Loogle: quoted "koszul": zero hits.
- LeanSearch: "negative shifted Koszul tail with augmentation and powers
  transition maps": service Internal Server Error, recorded unavailable, no verdict.
- rg in Mathlib AlgebraicGeometry and Algebra/Homology, WeilConjectures and
  lean/Sheaf for represent/cohomology, koszul and principal-open derived phrases:
  generic Koszul signs, the project full Koszul complex, projective-line
  three-term Koszul sequence, and KoszulAffineDetection. I inspected their types:
  none defines this tail system or proves this universal cohomology comparison.
- DAG rg and `blueprint_refs.py search Koszul`: the intrinsic completion nodes
  define full complexes and inverse limits, not this tail. The principal-unit
  and Cech statement nodes describe tails but have no definition declaration.
  dag/lean_names_upstream.json gives no existing declaration for this system.

New node review: def-sc-koszul-open-system is the concrete construction in Tag
08CX and the Hom diagram in Tag 08DC. Its dependencies are the existing scheme,
full Koszul complex and derived category. I checked the title, TeX, source,
three search kinds (including explicitly unavailable LeanSearch), created record,
chapter/unit, ancestor/via, empty proof fields and none audits against §5. The
item cites it. No dependency replacement module is needed. Every helper theorem
has a named source/docstring/proof and `sorry`; no definition has postponed data.
The tilde wrapper transports Mathlib's functor rather than inventing another
associated sheaf. Both module/docstring tags, line widths and names conform.

Mismatch repaired: the new definition node mentioned the Hom target E without
introducing it. I added `For E in D(O_X)` to that node's TeX statement. This
clarifies its existing Lean parameter; the item's statement and both Lean modules
were already right and were left unchanged. No statement correction or citer
verdicts are needed for the item. The earlier second-reading placeholder makes
no independent-review claim and remains as historical report text.

Validation: both delivery modules compiled together in dependency order with
scompile.py, exit code 0 in 15 seconds, no errors or warnings. The main node's
lean.statement matches its file signature verbatim; the new node's signature
matches the tools' signature convention with section variables supplied by Lean.
