## Worker report

The module states the two conclusions of Stacks Divisors 02ND and 02NS(1) for the
canonical ordinary blowup, with a sorry proof and the full DAG proof in its docstring.

Hypothesis and conclusion correspondence:
- Integral scheme T: `{T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral T]`.
- Quasi-coherent ideal in the structure sheaf: `I : T.IdealSheafData`, the existing
  affine ideal/localization encoding. Its associated module is `I.toModules`.
- Nonzero: `_hI : I ≠ ⊥`, where bottom has zero ideal on every affine open.
- Quasi-coherent and finite type: `_hft : I.toModules.IsQuasiCoherentFiniteType`.
  The recorded predicate unfolds to quasi-coherence and finite type, the latter
  equivalent on affines to finite generation; it imposes no finite presentation.
- Ordinary blowup B and its structure map b: `I.blowup` and `I.blowupMap`.
- B integral: `AlgebraicGeometry.IsIntegral I.blowup`.
- b projective in the required bundle convention:
  `AlgebraicGeometry.IsProjectiveBundle I.blowupMap`.

Statement dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup and blowupMap.
- Sheaf.AlgebraicGeometry.CoherentFiniteType:
  Scheme.Modules.IsQuasiCoherentFiniteType.
- Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism: IsProjectiveBundle.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module: toModules,
  whose sections identify with the original affine ideals.
All recorded available proof-dependency modules are imported. The sheaf-Rees node
has no recorded Lean declaration, so there is no module to import for it.

Edge cases checked: the empty scheme is excluded by IsIntegral itself, not by an
extra hypothesis. The zero ideal is explicitly excluded as in 02ND. The unit ideal
is allowed: its blowup is the identity. Zero generators give empty charts without
excluding a nonzero ideal. No proper-ideal, Noetherian, separated, excellence,
dimension or characteristic assumption is present. Universe u is arbitrary.

Searches:
- msearch leanfinder: "The blowup of an integral scheme along a nonzero finite type
  quasi coherent ideal is integral and projective" returned eight normalization,
  integral-morphism and Proj-properness results, none the statement.
- msearch loogle: "AlgebraicGeometry.Scheme.IdealSheafData.blowup,
  AlgebraicGeometry.IsProjectiveBundle" returned no match (unknown blowup identifier).
- msearch grep: "blowup|IsProjectiveBundle" in AlgebraicGeometry returned zero hits.
- rg in upstream WeilConjectures and project lean/Sheaf for blowup together with
  integral/projective, and for the node id, found affine projective embeddings,
  properness, and stronger specialized normalized-blowup statements, none this lemma.
  The upstream Proper module explicitly says projectivity remains unformalized.
- Read the source statements and proofs in divisors.tex at lemma-blow-up-integral-scheme
  and lemma-blowing-up-projective; both agree with the node.

No new nodes, dependency repairs or statement correction are required.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
