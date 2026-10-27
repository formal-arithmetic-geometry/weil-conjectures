## What changed

Replaced the single hole in DiagonalUniformizerScalarFrame by a complete Lean
assembly from two smaller comparison statements. The existing theorem signature,
the ScalarFrame fields, and both existing public imports are unchanged.

The proved theorem diagonal_flat_scalar_endpoint_iso in the new module
DiagonalFlatScalarEndpoint gives a unique normalized comparison for an arbitrary flat
internal module from the K-flat single-complex scalar adjunction. It explicitly
checks the ordinary/derived single-unit equation. Regular endpoints use the unique
ordinary scalar multiplication isomorphism. The actual integral Tate lines are
flat by spTwists_locallyFree, the signed-line tensor equivalence, and the
internal/section module flatness equivalence. Invertibility of l is transported
from global sections to the two schemes and their residue fields.

The assembly applies one arithmetic comparison to q, p1 and p2, and one geometric
supported-source comparison to both projections. A proved uniqueness lemma for
endpoint homs makes the independently obtained supported endpoints agree.

The generic ScalarSquareIsomorphisms structure shares coefficient and category
instances before specialization to the concrete quotient. Local irreducibility
annotations keep the canonical derived models and mate definitions compact during
elaboration; no shared reducibility attribute is changed.

Only the item module, three new modules and their nodes, and the item's proof-route
node are changed. No shared definition, source-library declaration, existing
statement, public import, or other existing module is changed.

Validation: all four modules compiled individually in import order through
lcompile.py. There are no development options or checkpoint commands in the
packet. The delivery command runs the final compiler and mechanical checks.

## Proved and sorry left

Closed the existing hole
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_scalarFrame
(node lem-diagonal-uniformizer-scalar-frame). There is no sorry in the item
module. This is a decomposition, not an axiom-free proof of the scalar frame:
one upper hole is closed and two lower holes are added (net minus one).

Also proved
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_flat_scalar_endpoint_iso
(node lem-diagonal-flat-scalar-endpoint), with no sorry. The frame's private
endpoint constructor chooses only its uniquely specified isomorphism.

The two new holes are:

- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_uniformizer_scalar_squares
  in Sheaf.Paper.DiagonalUniformizerScalarSquares
  (node lem-diagonal-uniformizer-scalar-squares).
- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_supported_scalar_source
  in Sheaf.Paper.DiagonalSupportedScalarSource
  (node lem-diagonal-supported-scalar-source).

Each is a public theorem in its own module with a complete proof in words and
exactly := by sorry. There are no hollow definitions or additional holes.
The arithmetic theorem has neither endpoint nor supported-source data. The
geometric theorem has no quotient arithmetic or line comparison; it handles one
retraction at a time. Neither is the original frame assertion under a new name.

## No longer needed

No original import is removed. The original public imports are retained verbatim.
Sheaf.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative remains needed
through the proved DiagonalFlatScalarEndpoint module and is not globally pruned.

The item's proof no longer uses sk-lem-geo-p1-cohomology
(Sheaf.AlgebraicGeometry.GeoP1Cohomology): the uniformizer quotient is a perfect
two-term coefficient complex, so its scalar mate commutes with every direct image.
The unit's projective-line cohomology route remains available elsewhere; no unit
statement or realized proof step is withdrawn.

The direct dependency lem-pur-twist-sheaf-locally-free
(Sheaf.Paper.PurTwistSheafLocallyFree) is replaced by
lem-route-sp-twists-locally-free (Sheaf.Paper.ProEtaleTateTwists), which states
local freeness for the actual integral twist used by this module.

The constant-coefficient closed-flat declaration
lem-pur-proetale-closed-pushforward-flat
(Sheaf.AlgebraicGeometry.ProEtaleClosedPushforwardFlat) is not imported: its
coefficient encoding differs from the internal condensed modules here. The
closed/open flatness argument is recorded in the new supported-source node.
lem-sf-ring-sheaf-closed-localization remains needed there; it is not globally
pruned. No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The planned local-freeness and closed-flat declarations do not directly have the
coefficient types of the actual spIntegralTwist and supported internal module.
The actual twist local-freeness theorem and the internal/section equivalence
resolve the former mismatch.

integralFiniteScalarPerfectModel already proves the perfect scalar argument,
including all-complex geometric mates. Its integer ring and its adjunction-mate
presentation differ from the actual PadicAlgCl.integers, quotient map, and
full-unit RestrictionSquare used here. The new arithmetic node isolates that
comparison and gives the direct rank-one resolution proof as well. Exact
coefficient restriction must not be assumed to preserve injectives when the
quotient is nonflat.

The supported-source theorem needs the ordinary composition normalization, not
just an unspecified isomorphism of source objects. The new node includes the
scalar-adjunction and full-derived-unit equation that fixes this normalization.

The new statements were checked on n = 0, ramified uniformizers, empty schemes,
and zero coefficient rings where applicable. No statement dispute was found.

The frame initially checked every proof but exceeded the compile limit at 64 s.
After using irreducible local wrappers and a generic assembly lemma, the
self-contained K-flat endpoint proof was moved into its own proved module. This
changes no existing interface and adds no hole.

## New nodes

lem-diagonal-flat-scalar-endpoint: a fully proved unique normalized scalar
isomorphism on a flat single internal module. It supplies a reusable interface
and separates the self-contained K-flat computation from frame assembly.

lem-diagonal-uniformizer-scalar-squares: the normalized restriction square and
invertibility of its mate for the actual uniformizer quotient, using its two-term
finite free resolution. It is independent of Tate lines, supported sources, class
maps and traces.

lem-diagonal-supported-scalar-source: the supported scalar endpoint, normalized
source and source-mate equation for one diagonal retraction, for arbitrary
coefficient maps. It is independent of uniformizer arithmetic and line
cohomology.

No change record is required: every existing signature and definition is retained.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
