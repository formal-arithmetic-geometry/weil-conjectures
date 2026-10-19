## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProjectiveBundleMorphism.lean` defines
`AlgebraicGeometry.IsProjectiveBundle`.  For schemes `X S : Scheme.{u}` and a morphism
`f : X ⟶ S`, its definition is

```lean
def IsProjectiveBundle {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (hE : E.IsQuasicoherent), E.IsFiniteType ∧
    ∃ (i : X ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProj),
      IsClosedImmersion i ∧
        i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom = f
```

The first binder `E : S.Modules` is the quasi-coherent `O_S`-module.  The second
binder `hE : E.IsQuasicoherent` renders quasi-coherence, and `E.IsFiniteType` renders
finite type.  The inner witness `i` is a morphism from `X` to the canonical relative
Proj of the symmetric graded algebra of `E`; `IsClosedImmersion i` renders the closed
subscheme clause; the final equality says that composing `i` with the relative-Proj
structure morphism gives the original `f`.  The canonical graded algebra is the
construction from `SymmetricAlgebraSheaf.gradedAlgebraData`, so no extra arbitrary
algebra, grading, gluing datum, or local-freeness assumption is introduced.

Dependency declarations used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `pqf-def-coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; the `IsQuasicoherent` and `IsFiniteType`
  predicates used by the definition are the corresponding Mathlib predicates on
  `S.Modules`.
- `def-nagata-relative-proj`: `AlgebraicGeometry.Scheme.GradedAlgebraData.relProj` and
  `relProjHom` from `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`.
- `lem-weil-pbc-quasi-coherent-symmetric-algebra`:
  `AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra` from
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`, with the canonical
  sectionwise construction supplied by the canonical symmetric graded algebra module.
- `lem-weil-pbc-symmetric-algebra-graded`:
  `SymmetricAlgebra.graded_by_tensor_images` from
  `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- `def-trf-canonical-symmetric-graded-algebra`:
  `AlgebraicGeometry.SymmetricAlgebraSheaf.gradedAlgebraData` from
  `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`.

Edge cases checked against the statement and source convention: `E = 0` gives the
empty projective bundle; `E = O_S` gives a projective bundle isomorphic to `S`;
`E = O_S^{n+1}` gives projective `n`-space over `S`; finite type does not imply local
freeness, so non-locally-free quasi-coherent modules remain allowed; and an empty base
has only the empty source.  No condition requiring `A_0 = O_S` is imposed on the
relative Proj input.

Searches made:

- `msearch.py ... leanfinder "Definition of EGA projective-bundle projective morphism by closed immersion into a projective bundle"`: eight Mathlib hits about ordinary `Proj` and its maps, no projective-bundle morphism predicate.
- `msearch.py ... loogle "AlgebraicGeometry.IsProjectiveBundle, AlgebraicGeometry.Scheme.GradedAlgebraData.relProj"`: no hit for `IsProjectiveBundle` (the relative Proj declarations are in the project source).
- `msearch.py ... grep "IsProjectiveBundle|projective.?bundle|relProj" AlgebraicGeometry`: no matching Mathlib declaration.
- `rg` over `WeilConjectures/` and `lean/Sheaf`: no upstream `IsProjectiveBundle`; the project search only finds this module and separate finite locally free projective-bundle geometry. `grep -rn` for the node id in `WeilConjectures/` found no declaration.

The source is Stacks Project, Morphisms, Definition Tag 01W8(1), together with
Constructions, Definition Tag 01OB.  The final sentence in the blueprint records the
 distinction from the finite-projective-space (`IsHProjective`) convention.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
