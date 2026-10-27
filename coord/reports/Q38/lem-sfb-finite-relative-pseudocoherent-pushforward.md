## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteRelativePseudoCoherentPushforward` states
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_iff_finite_pushforward` with
one whole-proof `sorry`. The source is Stacks Tag 09UK,
`literature/stacks-project/more-morphisms.tex`,
`lemma-finite-morphism-relative-pseudo-coherence` (lines 16995–17015).
The source and the node agree; no statement correction or new notion is needed.

Hypothesis and clause correspondence:

- Schemes X, Y and S: `{X Y S : Scheme.{u}}`.
- Structural morphisms X → S and Y → S: `f : X ⟶ S` and `g : Y ⟶ S`.
- Both are locally finite type: `[LocallyOfFiniteType f]` and
  `[LocallyOfFiniteType g]`.
- A finite S-morphism π: `(π : X ⟶ Y) [IsFinite π]`, with
  `hπ : π ≫ g = f` expressing the S-morphism condition.
- An arbitrary integer degree: `m : ℤ`.
- K in D(O_X): `K : schemeDerivedCategory X`.
- Quasi-coherent cohomology in every degree: `hK : schemeDerivedQCohProperty X K`.
  This expands to the existing `SheafOfModules.IsQuasicoherent` on each homology sheaf.
- Relative m-pseudo-coherence of K: `IsMPseudoCoherentRelativeTo f m K`.
- The actual derived pushforward in D(O_Y): `(schemeDerivedDirectImage π).obj K`.
- Relative m-pseudo-coherence of the image, over the same base and same degree:
  `IsMPseudoCoherentRelativeTo g m ((schemeDerivedDirectImage π).obj K)`.
- Preservation and reflection: the conclusion is an `↔` between those two predicates.
- There is no Noetherian, boundedness, flatness, surjectivity or finite-presentation
  hypothesis. The derived categories are unbounded. The uniformly quantified
  `HasDerivedCategory.{w}` instance is exactly the existing relative predicate's
  localization interface for arbitrary schemes and their affine charts; u and w
  are explicit universes. It does not restrict the base or the complexes.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- The convention node def-pc-morphism-conventions has no declaration of its own;
  the relevant named convention is `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (read its full class signature).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` and `schemeDerivedQCohProperty`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the recorded
  `SheafOfModules.IsQuasicoherent`; the conjunction `IsQuasiCoherentFiniteType`
  is not assumed, since the node requires only quasi-coherence.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo`. Read both definitions and
  their docstrings; this is the specified existential affine-cover/closed-embedding
  notion, with covers allowed to depend on m.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` (the actual ringed-space derived image).

Proof dependencies already stated are imported without public visibility:
`schemeDerivedDirectImage_preserves_QCoh` from DerivedDirectImagePreservesQCoh,
`exists_affineQCohDerivedEquivalence` from AffineQCohDerivedEquivalence,
`schemeDerivedDirectImage_openRestriction` from DerivedDirectImageOpenRestriction,
`RingedSpace.exists_derivedModuleDirectImageComposition` from
RingedSpaceDerivedDirectImageComposition, and `RingedSpace.derivedModuleDirectImage`
from RingedSpaceDerivedDirectImage (all under WeilConjectures.AlgebraicGeometry).
`DerivedCategory.IsMPseudoCoherentRelativeTo` comes from
Sheaf.RingTheory.RelativeMPseudoCoherent. The affine permanence and affine-pair
Mathlib declarations are supplied by Finite, FiniteType and the proof import
Mathlib.AlgebraicGeometry.Morphisms.Separated. The nodes
lem-sfb-relative-m-pseudocoherence-derived-sections and
lem-sfb-finite-algebra-relative-m-pseudocoherence have no recorded Lean statement
at this reading, so there is no module to import for them. They are proof inputs,
not missing statement notions; their use is spelled out in the theorem docstring.

Edge cases checked against the statement and source:

- π = identity yields invariance under the structural-map equality.
- Empty X is allowed, as is empty S (then X and Y are empty); no nonemptiness
  or surjectivity has been introduced.
- K = 0 is allowed; its relative property and the image's agree in every degree.
- All integers m, including zero and negative integers, are quantified unchanged.
- Non-Noetherian bases and complexes with no global cohomological bound are allowed.
- Finite maps need not be flat or closed immersions; neither property is assumed.
- The two base maps need not be globally finite type or quasi-compact.

Searches executed using msearch.py Q38 and this item:

- leanfinder: `Finite pushforward preserves and reflects m pseudo coherence of
  complexes relative to a base scheme`: 8 hits, consisting of finite/quasi-finite
  permanence, finite-type base change and ordinary pushforward composition;
  no relative derived pseudo-coherence theorem.
- leansearch: `Finite derived pushforward preserves and reflects relative m pseudo
  coherence`: 8 hits about ordinary pushforward, additivity and its section maps;
  no match.
- loogle: `"IsMPseudoCoherentRelativeTo"`: 0 hits.
- grep: `finite.*[Pp]seudo|[Pp]seudo.*finite`: 25 Mathlib hits concerning unrelated
  pseudoprimes and pseudometric spaces; no match.
- rg of the same pattern, the expanded pseudo-coherence pattern, and
  `IsMPseudoCoherentRelativeTo` in lean/WeilConjectures and lean/Sheaf: the relative
  definition and closed-immersion comparison are relevant, but no general finite
  pushforward theorem exists. ClosedSupportRelativePseudoCoherence is the special
  closed-immersion result, not this finite-map assertion.
- grep of this exact node id in lean/WeilConjectures: no result.
- rg of relative pseudo-coherence / finite pseudo-coherence names in
  dag/lean_names_upstream.json: no exact theorem.

The example Sheaf.CategoryTheory.CompactObject module is withdrawn; its node now
points to WeilConjectures.CategoryTheory.CompactObject. Read that actual definition
and its module/docstring conventions instead. No repair-note file exists for this item.
No STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the delivered file both in sandbox and in its
library module position cleanly (7.9 s and 5.6 s). No diagnostics remain.

## Second reading by Q38

I reread the node, source and final signature after compilation. The two structural
maps have separate locally finite type instances; hπ supplies precisely compatibility
with S; hK is quasi-coherence of all homology sheaves, not coherence or finite type.
The conclusion compares the relative predicates on X and Y with the same m and base,
using the actual derived direct image. The universal derived-category instance is
inherited unchanged from the recorded relative definition. The empty-scheme, zero
object, arbitrary-degree and unbounded cases remain present. No mismatch was found
and no correction was made. This is a self-check by the dispatched worker; no second
agent was started, as the dispatcher prohibits that. The maintainer's independent
review remains the independent reading of this delivery.
