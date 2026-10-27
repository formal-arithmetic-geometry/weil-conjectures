# Worker report: lem-trf-perfect-source-evaluation-quasi-isomorphism

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-perfect-source-evaluation-quasi-isomorphism.json` — existing item, split into seven proof steps; no new node.
- `citations.json` — verbatim statement quotes for every step dependency.

Attachments: none.

WANTED: none.

The item was not already declared by the upstream Lean source: searching `lean/WeilConjectures/` for the item tag and for perfect-source evaluation declarations found related perfect-complex interfaces but no declaration with this statement. The existing DAG already contains the finite-projective module tensor–Hom equivalence, projective-source derived-Hom model, K-flat tensor model, K-injective Hom invariance, and normalized one-K-flat uncurrying comparison, so I created no duplicate node. I corrected only the imported JSON's doubled TeX backslashes and literal `\\n` escapes; the mathematical statement and its dependencies were retained.

## Review by Q88

I read the item source, Stacks Project `more-algebra.tex` Tag 0ATK (lemma-internal-hom-evaluate-tensor-isomorphism, case (1)), its explicit chain-level construction Tag 0BYM (lemma-diagonal-better), Tag 0BYN (lemma-internal-hom-diagonal-better), and Tag 0A66 (lemma-RHom-out-of-projective). I also read the statements of every cited DAG node. Step 1 uses the product Hom and direct-sum total tensor definitions and checks the differential term by term, including the absence of an additional interchange sign. Step 2 uses the perfect-object definition, the bounded-above projective source map theorem, the derived localization/cohomology definition, and the K-injective Hom invariance statement; these give a chain representative `a : P → M`, its quasi-isomorphism property, and the two precomposition quasi-isomorphisms. Step 3 uses the Hom and tensor definitions, finite generation, and the finite-projective tensor–Hom equivalence. I checked the finite-support argument: boundedness of `P` makes the source degree a finite sum, and finite generation of each `P^s` makes maps into the direct sum have finite support. Step 4 uses the existing projective-source derived-Hom comparison and the fact that localization is detected by cohomology; the target map `q` is a quasi-isomorphism, so `H(P,q)` is one.

Step 5 reads the exact statements of K-flatness and the derived localization. It identifies the precomposition square and checks both composites on a homogeneous tensor, then uses K-flatness of `F` and the two vertical quasi-isomorphisms. Step 6 uses projective implies flat, bounded-above flat implies K-flat, the one-K-flat uncurrying normalization, the K-flat tensor model, and the native tensor associator/unit formulas. I checked that the transpose is explicitly `(f ⊗ h) ⊗ x ↦ q(f ⊗ h(x))`, so the coefficient map is exactly `Qq` after the counit. Step 7 uses the derived internal-Hom and tensor–Hom adjunction statements and checks contravariant naturality under `Qa`; its square is the localization of Step 5, so the canonical derived comparison is identified with `Q(t_M)`.

I checked all hypotheses at their use: `P` is bounded and finitely generated projective by perfectness; `F` is K-flat; `J` and `I` are K-injective; and `q` is a quasi-isomorphism. The edge cases include an empty or zero perfect source (the finite direct sums are then zero and the map is the unique isomorphism on zero complexes), a one-term finite free source (Step 3 reduces to the ordinary module tensor–Hom equivalence), and unbounded `F,J,I,M` (only `P` is bounded, while the finite-support argument handles each degree). Mathlib searches were rerun for LeanSearch, Loogle, LeanFinder, and grep; no Mathlib declaration states the derived perfect-source comparison. The server `review_split.py` preflight passed with zero new nodes.
