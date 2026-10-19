## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianSymmetricProductFiniteSurjective`
states `AlgebraicGeometry.symmetricProduct_finite_surjective_of_isNoetherian`.
Its single theorem has proof `sorry`; no new definition or proof is introduced.
The node is unchanged except for its `lean` record.

Clause-by-clause correspondence:

- “For a Noetherian scheme S”: `(S : Scheme.{u}) [IsNoetherian S]`.
  Mathlib's `IsNoetherian` means locally Noetherian and quasi-compact.
- “n ≥ 1”: `(m : ℕ)` represents every positive integer uniquely by `n = m + 1`.
- “(P¹_S)^n”: `X : Over S`, projections
  `pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{u} (Fin 2); S) ↘ S))`,
  and `hprod : IsLimit (Fan.mk X pr)` specify the fibre product by its universal
  property. This includes the inductively constructed product up to its unique
  projection-preserving isomorphism, exactly as in the recorded dependency interfaces.
- “Pⁿ_S”: `ℙ(ULift.{u} (Fin (m + 2)); S)` has n+1 homogeneous coordinates.
- “the symmetric-product map σ_n”: `ProjectiveSpace.homOfGeneratingSections` of
  `symmetricProductLineBundle (fun i ↦ (pr i).left)` and
  `symmetricProductCoordinateSection (fun i ↦ (pr i).left)`.
  These are the actual existing tensor bundle and coefficient sections, with
  `F_j` the coefficient of `t^j` in `∏ᵢ (x_i t + y_i)`.
  `Classical.choose` extracts only proofs of invertibility and generation from
  `symmetricProduct_properties S m X pr hprod`, never arbitrary morphism data.
  Both conjuncts contain the identical canonical morphism expression.
- “finite and surjective”: `IsFinite (...) ∧ Surjective (...)`.
  Read the full Mathlib class signatures: finiteness means affine with finite ring
  maps over affine opens; surjectivity is surjectivity of the underlying point map.
  These are exactly the conventions recorded by def-weil-pbc-scheme-conventions,
  which is a convention-only node with no module or declaration to import.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SymmetricProductPolynomial`,
  `AlgebraicGeometry.symmetricProductPolynomial`: imported publicly through
  SymmetricProductProperties; its coefficient ordering agrees with the sections.
- `Sheaf.AlgebraicGeometry.SymmetricProductProperties`,
  `AlgebraicGeometry.symmetricProduct_properties`: public import; its full signature
  and proof docstring supply the product interface and generating pair.
- `Sheaf.AlgebraicGeometry.SymmetricProductSections`,
  `AlgebraicGeometry.symmetricProductLineBundle` and
  `AlgebraicGeometry.symmetricProductCoordinateSection`: available via Properties.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`,
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`: available via Properties;
  its genuine fibre-product construction supplies the canonical map.
- `Sheaf.AlgebraicGeometry.SymmetricProductFinite`,
  `AlgebraicGeometry.symmetricProduct_finite`: proof-only import, first conjunct used
  in the documented proof plan with the identical generating pair.
- `Sheaf.AlgebraicGeometry.SymmetricProductSurjective`,
  `AlgebraicGeometry.symmetricProduct_surjective`: proof-only import; its existential
  witnesses are proofs in Prop, so proof irrelevance identifies its map with ours.
- Mathlib.AlgebraicGeometry.Noetherian (`AlgebraicGeometry.IsNoetherian`),
  Mathlib.AlgebraicGeometry.Morphisms.Finite (`AlgebraicGeometry.IsFinite`),
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap (`AlgebraicGeometry.Surjective`).

Edge cases checked before writing: n=1 (m=0) is the single-factor product;
its coefficient map reverses the two coordinates and is an isomorphism. n=0 is
excluded by the node and by m+1. The empty Noetherian base is allowed, with empty
source and target, so surjectivity is vacuous and finiteness holds. No nonemptiness,
reducedness, field, or characteristic assumption is introduced. Repeated factors
in positive characteristic cause no problem: the assertion is finite and surjective,
not etale. The universe u is explicit and arbitrary; ULift merely places the finite
coordinate sets in the scheme universe and does not change their elements.

Searches (2026-10-15):

- msearch.py leanfinder: “For a Noetherian scheme S the symmetric product morphism
  from n projective lines to projective n space is finite and surjective”. Eight hits
  on proper Proj maps, affine space and pointsPi; none states this conclusion.
- msearch.py loogle: `"symmetric", "finite"`. Six unrelated results on symmetric
  linear maps and monoidal categories; no match.
- msearch.py grep: `symmetricProduct|symmetric.product`. Five unrelated text hits
  in Dold-Kan, Clifford algebra and Data.Sym; no scheme morphism match.
- rg with the same pattern in upstream WeilConjectures and project lean/Sheaf:
  upstream has no match; the project contains the separate general finite and
  surjective lemmas and their construction, but no combined Noetherian statement.
- grep for the exact node id in upstream WeilConjectures: no match.

Read the original blueprint node at the recorded source path. Its statement agrees
with the DAG statement; the DAG's current proof specializes the two general lemmas.
No statement dispute, correction, missing notion, or unusable dependency was found.

Validation: scompile.py compiled the sandbox probe and delivered library module
cleanly (2.0 s and 2.2 s). deliver2.py --no-push printed OK: compilation and preflight
passed except for the independent second reading, which the next worker writes.
Nothing pushed. No local compiler or library build used.

## Second reading by NQ

Step-1 list and verdicts:

- A Noetherian scheme `S` is rendered by `(S : Scheme.{u}) [IsNoetherian S]`; this matches the node and adds no finiteness or field hypothesis.
- The integer `n ≥ 1` is rendered as `m : ℕ`, with `n = m + 1`; this covers every positive integer and excludes `n = 0` exactly as required.
- The source `(P¹_S)^n` is rendered by `X : Over S`, projections `pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{u} (Fin 2); S) ↘ S))`, and `hprod : IsLimit (Fan.mk X pr)`. This is the stated fibre product by its universal property.
- The target `Pⁿ_S` is rendered by `ℙ(ULift.{u} (Fin (m + 2)); S)`, giving exactly `m + 2 = n + 1` homogeneous coordinates.
- The map `σ_n` is the identical canonical `ProjectiveSpace.homOfGeneratingSections` expression built from `symmetricProductLineBundle` and `symmetricProductCoordinateSection`; the witnesses are proposition proofs selected from `symmetricProduct_properties`.
- The conclusion is exactly `IsFinite σ ∧ Surjective σ`, with Mathlib's finite morphism and underlying-point surjectivity predicates.

Edge cases checked: `m = 0` gives the one-factor map; `n = 0` is excluded; empty Noetherian bases remain covered; zero/repeated factors and positive characteristic introduce no extra assumptions; the explicit universe and `ULift` do not exclude cases from the node. Empty index products are represented by the stated `Fin` type.

Searches were rechecked with `rg` in project Lean and upstream WeilConjectures, and the recorded leanfinder/Loogle/grep searches. No existing declaration states this combined theorem; the separate finite and surjective dependencies are the correct interfaces. Dependency signatures and source tags were read; no mismatch, missing object, hollow definition, or statement correction was found. No changes to the worker module or node were necessary.

The required `scompile.py` check passed for the module (sandbox and library compilation, no errors). `deliver2.py --no-push` is the remaining dry run.
