## Worker report

This delivery states `Padic.exists_normOne_finiteSubfield_projection` in
`Sheaf.NumberTheory.Padics.NormOneFiniteSubfieldProjection` with proof `sorry`.
The node's natural-language statement, dependencies, and seven proof steps are unchanged.
The full compact-ball and maximal-graph proof plan is in the theorem docstring.
No new definitions or dependency repairs are needed.

Hypothesis and clause correspondence:

- A prime ℓ: `(l : ℕ) [Fact l.Prime]`.
- The ℓ-adic field: Mathlib `Padic l`.
- An arbitrary fixed algebraic closure: `(Ω : Type u) [NormedField Ω]`
  and `[IsAlgClosure (Padic l) Ω]`. The universe is explicitly bound.
- The extending absolute value and its norm topology:
  `[NormedAlgebra (Padic l) Ω]` gives the specified scalar embedding with its norm;
  `[IsUltrametricDist Ω]` expresses the given nonarchimedean inequality.
  The normed-field topology is the topology required by the node.
- A finite intermediate extension: `(F : IntermediateField (Padic l) Ω)` and
  `[FiniteDimensional (Padic l) F]`. The scalar action and inclusion are canonical.
  Its norm is the restriction from Ω, hence agrees with the coefficient-extension
  absolute value by uniqueness. No arbitrary map or topology is supplied.
- Existence and F-linearity of the map: `∃ p : Ω →L[F] F`.
- Retraction on every element of F: `∀ a : F, p (a : Ω) = a`.
- Sharp bound on every element of Ω: `∀ x : Ω, ‖p x‖ ≤ ‖x‖`.
- Continuity is bundled in `→L[F]`; for this linear map it is a consequence of
  the displayed bound, so this does not strengthen the node.
- No completeness of Ω: no `CompleteSpace Ω` binder occurs.

Dependency declarations read and used:

- `def-weil-algebraic-closure`: `IsAlgClosure`, from
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, exposed by the imported
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `def-weil-l-adic-numbers`: `Padic`, from
  `Mathlib.NumberTheory.Padics.PadicNumbers`, exposed through the recorded
  coefficient-extension dependency.
- `def-weil-l-adic-coefficient-extension`: imported its recorded module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and read
  `Padic.finite_coefficientExtensionRing` and the underlying
  `Padic.coefficientExtensionAbsoluteValue` in
  `Sheaf.NumberTheory.Padics.CoefficientExtension`. The current statement only
  uses the finite-dimensional extension and its inherited norm, not its integers.
- Proof dependency `lem-weil-l-adic-extension-absolute-value`:
  `spectralNorm_unique_field_norm_ext`,
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` (exposed by the coefficient module).
- Proof dependency `lem-weil-l-adic-extension-proper`: `FiniteDimensional.proper`,
  `Mathlib.Analysis.Normed.Module.FiniteDimension` (plain proof import).
- Proof dependency `lem-sfb-compact-closed-finite-intersection`:
  `CompactSpace.iInter_nonempty`, `Mathlib.Topology.Compactness.Compact`.
- Proof dependency `lem-weil-pbc-zorn-lemma`: `zorn_subset`, `Mathlib.Order.Zorn`.

Edge cases checked: ℓ = 2 is included; 0 and 1 satisfy the proposed bound, with
identity at 1 forcing norm exactly one. The bottom intermediate field is included.
There is no positivity condition on an extension degree beyond being a field.
An empty finite ball family still has B_0 nonempty; the empty Zorn chain is bounded
by the identity graph. The ambient algebraic closure is not completed. Arbitrary
ambient universe u is allowed; an intermediate field is a subtype of that same Ω.
No finite-dimensionality of Ω over F or the base is assumed.

Searches made with the prescribed wrapper:

- LeanFinder: “Norm one linear projection from a p-adic algebraic closure onto a
  finite intermediate field”: eight hits, including `PadicAlgCl.normedField`,
  `PadicAlgCl.norm_extends`, and `PadicAlgCl.spectralNorm_eq`; no projection theorem.
- Loogle: `"exists_extension_norm_eq"`: three hits. Read
  `Mathlib.Analysis.Normed.Module.HahnBanach`, lines 36–51: the scalar field must
  satisfy `IsRCLikeNormedField`, so it does not give this p-adic assertion.
  The other hits concern real-valued Tietze extension.
- Mathlib grep in Analysis:
  `norm.one.*(projection|retraction)|Ingleton|[Ss]pherically[Cc]omplete`:
  case-insensitive Ingleton matched singleton, producing irrelevant hits.
  Repeated with `\bIngleton\b|[Ss]pherically[Cc]omplete|nonarchimedean.*(retract|projection)`:
  zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `norm.one|norm_one|finiteSubfield|finite_subfield|NormOne|normOne`:
  only the related `Padic.exists_finiteSubfield_continuousLinearRetraction`
  is a candidate. Its full signature and docstring were read; it asserts only
  E-linearity and continuity and explicitly does not assert a norm bound.
  Thus it is strictly weaker than this item and cannot be an existing match.
- The prescribed node-id grep in `lean/WeilConjectures` found no match.

Source checked: the current blueprint main-20261015 direct-images proof, paragraph (3).
The projection is the agent-formulated analytic auxiliary input described by the node,
whose exact literature reference remains WANTED; no additional source claim is made.
No statement correction and no STATEMENT-DISPUTED flag.

Validation: `scompile.py` compiled the sandbox and library forms cleanly on the server
(3.4 s and 3.8 s), with no errors or warnings. The prescribed `deliver2.py --no-push` dry run passed preflight and compilation
(commit 7ab1e98ae64); delivery reruns those checks on this packet.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
