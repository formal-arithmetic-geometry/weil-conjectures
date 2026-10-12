## What changed

In WeilConjectures.SixFunctors.Integral.Exact, replaced the sole direct sorry in
AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj with a proof using the existing
stalk restriction map and the conservative family of geometric points. A proved private
helper, surjective_stalkRestrict_of_isIntegralHom, represents a source germ, pulls it back
to a pointed clopen piece, extends the section by zero on the complementary piece, glues
by the sheaf axiom, and verifies the germ using the stalk coprojection identities.

Added the proof-only import Sheaf.AlgebraicGeometry.IntegralPointedClopenRefinement.
This module states the remaining geometric refinement theorem, independently of sheaves,
coefficients or a zero-pushforward hypothesis. It preserves the marked geometric point,
which is needed to recover the prescribed germ rather than an arbitrary lift over its
underlying topological point. Neither public signatures nor definitions were changed.

Both modules compile together with the prescribed lcompile.py launcher. The deliver3.py
--no-push dry run also compiled on the server and printed OK; preflight has only the
second-reading section left for the independent reader, and nothing was pushed. The source is
allowed to be empty, the map need not be surjective, and its geometric fibre can be
infinite. For the identity morphism the neighbourhood itself supplies the piece, with
empty complement; for a finite morphism this is the existing pointed piece-refinement
construction. The proposed general geometric step descends the same finite construction
from a finite subalgebra of the integral algebra.

## Proved and sorry left

Proved, from the named geometric theorem:
AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj
(node lem-sbc-integral-direct-image-detects-zero).
The private helper surjective_stalkRestrict_of_isIntegralHom is completely proved.
There are no direct sorries left in the item's module. Its existing exactness and
conservativity proofs remain intact.

The delivery leaves exactly one direct sorry:
AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_clopen_refinement
(node lem-sbc-integral-pointed-clopen-refinement), in
Sheaf.AlgebraicGeometry.IntegralPointedClopenRefinement.
Thus zero detection and conservativity still depend transitively on this geometric step;
they are not yet closed under the project's axiom criterion.

## No longer needed

None. The existing public imports are used by the exactness proof and by the stalk
restriction construction. The new module's two imports supply the neighbourhood/open
inclusion interface and the base-change pointed-neighbourhood functor. No proof dependency
was discarded, and no unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No DAG node in the checkout had a lean.module record naming this source module. The
blueprint node sbc-lem-integral-etale-direct-image-exact concerns exactness, which was
already proved here; the only direct sorry is instead the conservativity subargument in
the proof of sbc-lem-bc-integral-base. Added a node for that existing declaration with its
actual proof route, rather than attaching zero detection to the exactness statement.

The geometric refinement needed to extend a prescribed germ was not separately stated
in the DAG. The new geometric node makes this step precise. The broad disjoint-cover
lemma already imported proves the epimorphism-preservation part, but does not specify
which lift of a chosen geometric point a piece maps to, so it cannot by itself supply this
pointed refinement.

LeanSearch returned Internal Server Error; the search records mark it unavailable.
LeanFinder and the Mathlib/source/DAG searches supplied no matching integral pointed
refinement theorem. No unavailable search was counted as proof of absence.

## New nodes

lem-sbc-integral-pointed-clopen-refinement: the sole remaining geometric step, stated
in lean/Sheaf/AlgebraicGeometry/IntegralPointedClopenRefinement.lean. Its source is the
finite-subalgebra/strict-henselisation paragraph of sbc-lem-bc-integral-base, with a full
proof in words and the existing algebra/descent nodes recorded as dependencies.

lem-sbc-integral-direct-image-detects-zero: records the already existing source declaration
AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj and its newly written proof. This
node keeps the extension-by-zero step and geometric-stalk detection explicit in the DAG.
No change record is needed: the import is proof-only, the helper is private, and all
existing public signatures and definitions are unchanged.

## Second reading by V1

1. Public interface: PASS. Read the complete diff against the repository's Exact.lean.
   All five existing declaration signatures, section variables, definitions and original
   public imports are unchanged. Only a private proved helper, a proof-only import and
   the body of isZero_of_isZero_lowerStar_obj were added. There is no statement or
   definition change requiring a change record.
2. Proof and compilation: PASS as a partial stage-3 proof. Both delivered modules compile
   in import order with lcompile.py, without errors or warnings. Scratch-copy
   #print axioms checks covered all five public declarations, the private helper and
   the new geometric theorem. The three existing exactness declarations use only
   propext, Classical.choice and Quot.sound. Zero detection, conservativity and the
   private helper additionally use sorryAx from the explicitly reported geometric
   theorem. That theorem is the only direct sorry in the delivery; no definition
   contains sorry and no forbidden declaration or implementation escape is present.
   Thus the one original direct sorry has been reduced, but zero detection is not
   yet proved under the final axiom criterion.
3. Split statement: PASS. The pointed clopen refinement is geometric and independent
   of coefficients, sheaves and the zero-pushforward hypothesis, so it is a strict
   part of the argument rather than a restatement. Checked the empty-source case
   (no t), identity case (restrict to a pointed neighbourhood and use empty Q),
   finite case (the pointed piece functor), and non-surjective/infinite-fibre cases.
   Integral algebras as filtered unions of finite subalgebras give the claimed route.
   In a finite factor over the strict henselisation, the residue field is purely
   inseparable over a separably closed field, hence itself separably closed; the
   prescribed geometric lift of the etale object is consequently residue-rational
   and has the required section. Descending its finite data preserves the chosen
   lift, not just the underlying point. The docstring and new node contain this
   argument and a source. Independently searched LeanFinder for henselian sections
   on clopen neighbourhoods, Loogle for IsIntegralHom (identifier unavailable there),
   Mathlib grep for henselian sections/refinements, and the repository's Lean files
   for clopen integral refinements. Read PieceRefine, DisjointCover, Stalk and the
   existing algebra/descent statements: none states this general pointed result.
   DisjointCover alone does not force its lift to equal v. Completing the geometric
   formalization requires more than a short repair; no new sorry was introduced.
4. Route and pruning: PASS. Read the germ representation, disjoint sheaf gluing,
   both point-preservation rewrites, epimorphism from a zero stalk, and conservative
   geometric-stalk argument. The new imports supply symbols in the new theorem's
   signature; the item imports it privately. The existing imports continue supplying
   exactness and the stalk interface. No old proof dependency or import is discarded,
   so No longer needed is complete. The sk-lem-universal-datum record already has
   empty realized entries in this checkout; this delivery does not change them or
   bypass any realized unit step. The conservativity argument follows the source
   paragraph stored in the existing sbc-lem-bc-integral-base node (the cited
   literature file itself is absent from this read-only checkout).
5. DAG: PASS. Read both new nodes, their sources, lean records, statements and proof
   steps, and the existing nodes they cite. The zero-detection node records clopen
   extension by zero followed by geometric-stalk detection; the geometric node
   records precisely the algebraic construction still left open. proof_deps equals
   the union of each node's step uses. Neither new node claims a replacement for
   the already proved exactness node. The new fields required by the stage-3 brief
   are present, and their module and declaration names agree with Lean.

Second reading changed only this report: added the independent checks and explicit
axiom-closure verdict. No Lean proof, statement, definition, import or DAG repair
was necessary. Temporary axiom-probe copies were removed before delivery.
