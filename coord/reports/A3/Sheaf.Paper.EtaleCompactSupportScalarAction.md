## What changed

Proved `AlgebraicGeometry.etaleCompactSupport_scalarAction` with its original signature.
All additional declarations are proved private helpers in the item module. There are no
new public definitions, instances, imports, or consumer changes.

Constructed ordinary scalar multiplication at each level from the actual constant-ring
sheafification unit. Naturality of the unit under site maps and coefficient quotient maps
proves compatibility with restrictions and successive system transitions. Localizing its
termwise natural transformation constructs the derived action with exactly the required
representative equation.

The normalized inverse-image lift preserves this action by its `moduleSMul` graph equation
and the prescribed constant-section comparison. The constant singleton is already a sheaf;
its sheafification unit is invertible, which verifies the constant-section formula on every
section, including empty objects. The inverse-evaluation isomorphism gives preservation on
ordinary systems. Naturality of the derived factorization and the localization universal
property extend this identity to all derived objects.

Finally, preservation of central natural endomorphisms transfers across an adjunction in
either direction by the Hom adjunction and naturality of its unit/counit. Apply this to the
recorded derived open and proper adjunctions and compose the resulting identities. This
avoids constructing a separate linear-category instance or making any new resolution choice.
The DAG proof and proof dependencies now record this argument.

Validation: the complete module compiled on the project server in 20.5 seconds.
Factoring scalar-map calculations over an abstract ring sheaf avoids repeated concrete
coefficient-sheaf unfolding during kernel checking; no time limit was changed.

The construction requires no regularity, completeness, nonzero ring, or nonempty scheme
hypotheses. In particular it includes `t = 0`, unit `t`, the zero ring, and empty schemes.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.etaleCompactSupport_scalarAction`
(node `lem-pur-etale-compact-support-scalar-action`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered Lean source. Every helper proof is complete.

## No longer needed

No module is withdrawn and no existing public import is removed. The item retains only its
original public import `Sheaf.Paper.StrictEtaleSystemInterfaces`; no proof import is needed.
The following former direct DAG dependencies are not used by this proof:

- `lem-weil-linear-abelian-derived-category`: localize the central natural transformation
  directly; a scalar-module structure on every Hom is unnecessary.
- `lem-pur-linear-localization-lift`: use `Localization.liftNatTrans`, its representative
  formula, and `Localization.natTrans_ext` directly instead of functor linearity.
- `lem-weil-pbc-extension-by-zero-adjunction` and
  `lem-weil-pbc-extension-by-zero-exact` (module
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`): use the ordinary and
  derived adjunctions already supplied by `StrictEtaleCompactSupport`.
- `lem-weil-pbc-exact-functor-derived-factorization`: use the inverse-image factorization
  already recorded in `CoefficientDerivedImage`; no new derived functor is constructed.
- `lem-weil-kinjective-total-derived-linear` (module
  `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear`): transfer preservation to the right
  adjoint using counit naturality, so no K-injective computation is needed here.
- `lem-sfb-grothendieck-k-injective` (module
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`): no resolution
  existence theorem is used by this proof.
- `lem-pur-coefficient-system-derived-comparison` as an existence theorem (module
  `Sheaf.Paper.CoefficientSystemDerivedComparison`): the compact-support datum supplies the
  required normalized functors. Its public definitions are still transitively imported by
  the unchanged interface; this is not a claim that the module leaves the target closure.

The replacement proof dependencies are the existing strict-system and image-data definition
nodes and `lem-weil-pbc-localization-universal-property`. This changes only the node-level
argument; every unit statement and its realized steps stay in place.

## Where the brief, the DAG or earlier work was wrong

The stated DAG dependencies describe the intended geometric argument but do not directly
construct an `O`-linear structure on this particular strict-system category. That structure
is unnecessary: the theorem only asks for canonical central natural transformations.
Both required derived adjunctions are already fields of the compact-support datum, so
transferring their central actions is shorter than the original separate K-injective proof.
The original declaration docstring records that older plan; the implementation and updated
DAG use the adjunction argument described above. No statement or definition was repaired.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
