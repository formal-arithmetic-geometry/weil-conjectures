## Worker report

The following original worker account is retained for history; the second reading below
rejects its formulation and proposed statement correction. The delivered node statement
is unchanged from the repository.

The module states `tensor_section_affine_open` for a finite index type, explicitly supplied tensor section, and its fibrewise defining nonvanishing property. It concludes the intersection equality and affineness when one factor locus is affine. The original node omitted the finite index and an iterated tensor construction, so the node is corrected with `statement_change`.

Dependencies used: `def-pc-scheme` (Mathlib `AlgebraicGeometry.Scheme`), `def-sc-invertible-module` (`AlgebraicGeometry.Scheme.Modules.IsInvertible`), `def-weil-pbc-ample-invertible-module` (`AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`), and `def-pur-sheaf-tensor-product` (`SheafOfModules` tensor API). The affine intersection theorem is `AlgebraicGeometry.Scheme.Modules.affine_cap_section_open`.

Edge cases checked conceptually: `n = 0` is excluded by the explicit affine factor `j : Fin n`; zero sections give empty loci; `n = 1` reduces to the given affine locus.

Searches: LeanSearch/LeanFinder and grep searches recorded in the node found no existing tensor-section affine theorem. `rg` over `lean/Sheaf` found only the affine-cap theorem and tensor APIs.

## Earlier proposed statement correction (rejected)

The old statement did not bind `n`, did not define an iterated tensor product for varying modules, and did not introduce the induced tensor section. The corrected statement follows the source's finite-family claim by making the index, tensor section, and fibrewise defining property explicit. The sole citer `lem-sc-enough-globally-generated-ample` continues to use the affine tensor-section fact (holds true).

## Earlier second reading (a previous round; superseded)

The Lean binders render the finite family, section data, fibrewise intersection condition, affine factor, equality, and affine conclusion explicitly. No proof beyond `sorry` is supplied.

## Second reading by J1

I read the original repository node, the worker's changed node and module, the source
Varieties 09NC proof at varieties.tex lines 7897–7924, and Properties 01PV at
properties.tex lines 4288–4313, retrieved read-only from the server because this clone
has only the literature indexes. The source constructs the actual finite tensor product
and pure tensor section. Properties 01PV assumes only a scheme, an invertible module,
a global section, and an affine open. Quasi-compactness and global generation belong
to the enclosing 09NC cover argument, not this generic intersection lemma.

Item-by-item inventory and verdict on the delivered statement:

- Object: an arbitrary scheme X [def-pc-scheme]. Rendered by `{X : Scheme.{u}}`.
  Mathlib's Scheme is a locally ringed space locally isomorphic to spectra
  (Mathlib/AlgebraicGeometry/Scheme.lean:42). Exact; no base field, separation,
  quasi-compactness, Noetherianity, or characteristic condition added.
- Objects: finitely many O_X-modules L_1,...,L_n. Rendered by `{n : ℕ}` and
  `L : Fin n → X.Modules`. Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:42 defines
  X.Modules as SheafOfModules over X.ringCatSheaf. Exact finite numbered family.
- Hypothesis: every L_i is invertible [def-sc-invertible-module]. Rendered by
  `[∀ i, (L i).IsInvertible]`. Read the recorded source declaration in
  WeilConjectures/AlgebraicGeometry/Modules/Invertible.lean:57: local isomorphism to
  the structure sheaf. Exact; this is Scheme.Modules.IsInvertible as required,
  not the separate SheafOfModules class. This hypothesis was missing in the worker file.
- Objects: global sections t_i. Rendered by
  `t : ∀ i, (L i).val.presheaf.obj (Opposite.op ⊤)`. Exact global sections over X.
- Objects: their tensor product and induced section tau [def-pur-sheaf-tensor-product].
  Rendered by the typed local `let τ : Σ M : X.Modules, ...`, whose value is the
  `List.ofFn` family folded with `⟨a.1 ⊗ b.1, tmulSection a.2 b.2⟩` and initial
  `⟨𝟙_ X.Modules, unitSectionsEquiv ⊤ 1⟩`. The first projection is the actual
  iterated tensor module; the second is its actual pure tensor section. Opened
  WeilConjectures/AlgebraicGeometry/Modules/TensorSection.lean: tmulSection is the
  image of the sectionwise pure tensor under sheafification. Also read the source
  Sheaf/Monoidal.lean tensorObjIsoSheafification and the recorded dependency module
  Sheaf/Algebra/Category/ModuleCat/Sheaf/TensorProduct.lean, which reuses that same
  monoidal structure. Right association with a final tensor unit differs only by
  the canonical associators and unitor; it changes neither the section nor its locus
  under those identifications. No private tensor-product definition or new notion.
- Objects: nonvanishing loci X_ti and X_tau [def-weil-pbc-ample-invertible-module].
  Rendered by the recorded `Scheme.Modules.nonvanishingLocus` from
  Sheaf/AlgebraicGeometry/Ample.lean: germ outside maximalIdeal times the stalk.
  Read that definition and Modules 01CY (modules.tex:4360–4374). Exact fibre
  nonzero condition on invertible modules; no assumption of ampleness introduced.
- Conclusion clause 1: X_tau is the intersection of all X_ti. Rendered by
  `nonvanishingLocus τ.1 τ.2 = ⋂ i, nonvanishingLocus (L i) (t i)`.
  Exact set equality, hence equality of the corresponding opens; unconditional,
  including the empty family. The worker had assumed this clause as `hτ`.
- Hypothesis for conclusion clause 2: some X_tj is affine. Rendered inside the
  implication by `∃ j : Fin n, ∃ U : X.Opens, IsAffineOpen U ∧
  (U : Set X) = nonvanishingLocus (L j) (t j)`. Exact affine-open condition,
  without a globally supplied index restricting clause 1.
- Conclusion clause 2: X_tau is affine under that hypothesis. Rendered by the
  consequent `∃ U : X.Opens, IsAffineOpen U ∧
  (U : Set X) = nonvanishingLocus τ.1 τ.2`. Exact; both clauses are conjoined
  after the finite family and sections, with the affine hypothesis only on clause 2.

Edge cases: for n = 0 the fold is the structure sheaf with section 1, whose locus is
all X; the empty intersection is all X, and the affine-factor antecedent is false.
No affineness of arbitrary X is claimed. For n = 1 the final unit is removed by the
canonical unitor. A zero factor section gives the empty tensor locus; the empty
scheme is allowed throughout and has no imposed point or nonemptiness instance.
Zero modules are excluded only where invertibility itself excludes them (on a
nonempty scheme); the zero object on an empty scheme is not artificially excluded.
The universe u is arbitrary, matching the dependency Scheme and X.Modules APIs;
Fin n places no further universe restriction on a numbered finite family. No
characteristic, domain, field, or nonzero-ring condition is imposed.

Independent searches (2026-10-11), with different wording from the first report:
LeanSearch via msearch for "nonzero locus elementary tensor sections invertible
modules intersection" returned UNAVAILABLE (Internal Server Error), so no search
verdict is inferred. LeanFinder via msearch for "vanishing locus pure tensor global
sections line bundles finite product" returned eight unrelated ideal-sheaf,
zero-locus, and ring-tensor results, no exact theorem. Loogle query `"tmulSection"`
returned zero Mathlib hits. Independently rg searched Mathlib/AlgebraicGeometry,
WeilConjectures/AlgebraicGeometry/Modules, lean/Sheaf/AlgebraicGeometry, DAG nodes,
and dag/lean_names_upstream.json for nonvanishing, vanishingLocus, tensorSection,
tmulSection, finite tensors and folds. The upstream tmulSection and
unitSectionsEquiv are the usable constructions, now reused; the project has the
binary affine-cap lemma but no theorem for this finite-family locus equality and
affine conclusion. Read the generating-locus API too: it gives local generation,
not the statement here. No duplicate theorem or new definition node is needed.

Mismatches repaired: rejected the worker's statement_change because absence of a
Lean construction does not make the original mathematical statement wrong. The
claimed "fibrewise defining property" only described a locus and did not identify
an induced tensor section; it assumed the first conclusion. Restored the original
node statement and removed statement_change. Replaced arbitrary T, tau and hτ
with the actual list-fold construction from the existing binary tensor API.
Added the missing invertibility hypotheses. Moved the affine-factor index and
condition into the second clause's implication, preserving clause 1 when n = 0.
Removed the unused AffineCapSectionOpen import (its theorem is a proof dependency,
not needed to type the statement), added TensorSection and List.OfFn imports,
added the project header, and expanded the theorem docstring to carry both node
proof steps with their cited dependencies. Every theorem proof remains `sorry`;
there are no new definitions or hollow data and no unbound variables/universes.
The node lean.statement is copied verbatim from the delivered signature.

The only external citer is lem-sc-enough-globally-generated-ample (opened its
statement and proof, especially steps 3 and 4). Its use holds: it constructs the
same finite pure tensor section and requires both its nonvanishing intersection
and the conditional affine conclusion. No second external citer exists; rg found
only that node and the item itself. Since the original statement is restored,
there is no delivered correction or change to any citer or unit statement.

Validation: the complete delivered module compiled cleanly on the server using
scompile.py (no errors or warnings). Delivery preflight is run after this review.

## Reviewer fix (R-tsa1325, stage 2)

The delivered statement built the iterated tensor product and its section with a private
`List.ofFn ... foldr` over `⊗`/`tmulSection`/`unitSectionsEquiv`: a second definition of
the notion landed by H1 as def-sc-positive-tensor-family (dd2dcde36,
`AlgebraicGeometry.Scheme.Modules.positiveTensorFamily` / `positiveTensorFamilySection`;
H4/H12). Restated with the landed declarations: `L : Fin (n + 1) → X.Modules`,
`t : (i : Fin (n + 1)) → (L i).sections`, τ = `positiveTensorFamilySection n L t`, loci
taken at `(·).val (Opposite.op ⊤)`. The family is nonempty (n + 1 factors), as in the
landed definition and def-pur-sheaf-tensor-product (tensor powers for m ≥ 1); the n = 0
case of the private fold (O_X with section 1, locus X) is no longer stated. Imports reduced
to Ample and PositiveTensorFamily; parentheses made explicit around the equality clause.
