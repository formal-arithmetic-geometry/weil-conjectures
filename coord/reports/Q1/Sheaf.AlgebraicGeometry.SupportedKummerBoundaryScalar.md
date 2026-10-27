## What changed

Proved `AlgebraicGeometry.Etale.supported_kummer_boundary_scalar`, preserving its
signature and public import. The supported source coefficient unit comes from
`supported_kummer_scalar_source`. The Tate-line Hom equivalence constructs the
normalized target coefficient map; flatness of the source line upgrades its
ordinary universal property to the unbounded derived one. Both normalized
boundaries have the same integral pole/Kummer equation. Testing on the integral
supported generator is injective on Ext and proves the coefficient square.

Three new modules contain fully proved components: the integral normalization,
the root-line coefficient unit, and their scalar-square assembly. These are not
new proof obligations. Local opacity controls and generalizing the argument over
abstract coefficient rings reduced repeated unfolding, but the combined file
still exceeded the limit in delivery. The integral normalization, root-line
construction and general assembly are now separate modules, as permitted by the
current brief. The assigned module only specializes to the lifted residue ring.
No existing shared definition or consumer is changed.

The proofs reuse private `lineHomEquiv`, its generator equation and
`finiteEtaleGenerator_smul` from `FiniteEtaleTateLinePullback`, plus
`generator_scalar` and cached instance witnesses from
`EtaleSupportedIntegralDerivedUnit`, through private `import all` proof imports.
All new data is explicitly constructed; the pole class is uniquely determined.
The local irreducibility attributes change no existing shared interface.

Validation: `lcompile.py --all` accepted all four delivered modules with no errors
or warnings. The original declaration signature is verbatim unchanged. All files
have zero `sorry` tokens, no debugging options and lines at most 100 characters.
Every node dependency exists, each proof dependency list equals the union of its
step uses, and no changed node introduces a cycle returning to itself.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.supported_kummer_boundary_scalar`.
Added zero holes. All three new public theorems are proved:

- `AlgebraicGeometry.Etale.supported_kummer_integral_equation`;
- `AlgebraicGeometry.Etale.supported_kummer_root_scalar_unit`;
- `AlgebraicGeometry.Etale.supported_kummer_scalar_of_source`.

No `sorry` remains in any delivered module. All private helpers are proved.
The original obligation is closed without adding lower obligations.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
  (`lem-asd-finite-etale-twist-line`): the proved tensor inverse supplies flatness.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
  (`lem-pur-derived-change-of-rings`): the proved flat scalar-unit API supplies
  the required unbounded universal property.
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`
  (`lem-amb-relative-torsor-cohomology`): integral pole-class uniqueness identifies
  the relative extensions directly.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
  (`lem-amb-kummer-any-base`): its separate import is redundant through the public
  boundary interfaces. Its Kummer sequence is still used and the node remains a
  dependency of the proved auxiliary statements.
- `Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence`
  (`lem-asd-cartier-boundary-existence`): reduced-boundary existence and uniqueness
  are unnecessary; the given classes are compared through their integral generator.

The first, second, third and fifth nodes are no longer direct mathematical
requirements of this argument. No module or upstream declaration is withdrawn;
other consumers and transitive imports may still use them. Existing proof APIs
used by the argument are imported by the appropriate auxiliary module. The unit
`sk-prop-sf-cbc` has no realized statement or steps bypassed by this route.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The previous plan's final functoriality step
is made explicit by the integral derived-unit Ext injection. The integral equation
requires neither finiteness of coefficients nor positivity of N. The root map
requires no flatness of the new coefficient ring. Empty support, empty schemes,
the zero ring and N=1 require no additional hypotheses.

The source has optional private finite-positive normalization helpers in
`CartierBoundaryScalarSquare` and `CartierReductionSiteComparison`. The former was
not yet available in the published build; the latter would create an import cycle.
Neither is imported or redeclared. The already developed general integral equation
is proved directly from the relative boundary specification and pole uniqueness.

## New nodes

`lem-asd-supported-kummer-integral-equation` is the proved integral normalization
component, sourced to the current blueprint's relative extension and coefficient
paragraphs (Stacks 03PL and 0A45). Evaluate the boundary specification on the
complementary open, identify the relative extension by pole-class uniqueness,
and substitute into its final Ext equation.

`lem-asd-supported-kummer-root-scalar-unit` is the proved normalized root-line
coefficient unit (Stacks 03PK and 07A6; the blueprint's final coefficient paragraph).
Construct it by the Hom equivalence, verify its pure-root formula and universal
property, and use the tensor inverse and flat scalar-unit theorem.

`lem-asd-supported-kummer-scalar-of-source` is the proved general assembly of the
given source unit and the root unit (Stacks 03PL and 07A6; the same paragraph).
The integral generator and root generator commute with the coefficient maps.
The two integral equations, exact-functor coherence and Yoneda associativity
identify the images under the integral Ext injection, which detects the square.

LeanSearch, LeanFinder, Loogle, Mathlib grep, and source/DAG/blueprint searches found
no matching public theorems for these isolated ordinary-site interfaces. The
existing component APIs are used directly. All nodes carry complete proofs and
Lean attachments; none adds a hole.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
