# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-analytic-projective-structure-cohomology.json`: item, split; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-analytic-projective-kahler-geometry.json`: new statement-only input, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-hartogs-punctured-affine-extension.json`: new statement-only input, unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quotation for each node cited by each numbered proof step.

The sandbox also contains the search command's `searches.jsonl`, the complete search answers, and the scripts that wrote these sandbox files. No Lean was written or compiled, no repository or launcher file was changed, and no git command was run by the worker.

## Attachments

None. The exact blueprint tag and the analytic notions were searched in `lean/WeilConjectures/`. The only nearby declarations concern algebraic projective space, algebraic Hartogs extension, or unrelated analytic constructions; none proves this item.

## WANTED

WANTED: Serre, Géométrie algébrique et géométrie analytique, §13 Lemma 4, printed pp.20--21, for lem-sfb-analytic-projective-structure-cohomology. The requested local `literature/serre-gaga.pdf` does not exist. Read the original online at https://www.numdam.org/article/AIF_1956__6__1_0.pdf.

WANTED: Demailly, Complex Analytic and Differential Geometry, I §3.D Theorem (3.28), printed p.28, for lem-sfb-hartogs-punctured-affine-extension; V §15.A, printed p.277, and VI §4 Example (4.4), printed p.297, for lem-sfb-analytic-projective-kahler-geometry. The local PDF is absent; read these places online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf. The source record is explicit about local availability. Nothing was downloaded.

## Issues found and corrected

Serre's Lemma 4 uses Dolbeault and then asserts that the (0,q) cohomology of projective space vanishes. This is the argument to expand, rather than a license to create a node repeating that vanishing. Its printed footnote discusses a different Laurent-series proof, but the split retains its Dolbeault/Kähler route. The item is true with exactly its existing hypotheses; no STATEMENT-DISPUTED correction is needed.

There is an important circularity hazard: `lem-sfb-projective-harmonic-representatives` has `lem-sfb-algebraic-dolbeault-derivative-comparison` as a proof dependency, which uses GAGA, whose proof uses this item. Consequently this split does not cite the projective harmonic-representative theorem, its algebraic-Dolbeault parent, or GAGA. It instead derives the needed representative and closedness directly from the independent Hermitian orthogonal decomposition and Kähler Laplacian identity. Those statements require only compact Hermitian/Kähler geometry and the already independent Dolbeault resolution.

The new geometric input states the metric, its overlap gluing, compactness, manifold properties, and explicit local sections of the quotient map. It is not a restatement of constant global functions or of higher structure-sheaf cohomology. Hartogs is stated for arbitrary functions in at least two complex variables, with no continuity assumption at the missing point. A one-variable removable-singularity theorem would not suffice.

The ancestor command returns `None` for this inherited support chain. Both new nodes retain that exact null ancestor, name the inherited current direct-images proof (3) support place and carry the required via chain. The latest blueprint direct-images proof and the recorded chapter/unit were read; no unit or chapter is changed. This item is a supporting prerequisite, not the statement of its unit, so no unit-realization field is written.

## Search review

Before creating the nodes I searched all DAG statements for Hartogs, Fubini--Study, holomorphic functions/forms, complex manifolds, and Kähler metrics, and searched the full blueprint with `tools/blueprint_refs.py search` for Hartogs, Fubini, holomorphic, harmonic, projective structure and extension of holomorphic functions. I read the nearby analytic nodes listed below, not only their titles. Searches of the project Lean source found no analytic Hartogs or Fubini--Study declaration.

For the item and each new node I ran two LeanFinder phrasings, LeanSearch, Loogle and grep through the required `msearch.py`, inspected their results, and recorded exactly those queries. Raw answers are retained. All services answered. Hartogs searches return one-variable `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` and bounded/little-o variants; I opened `Mathlib/Analysis/Complex/RemovableSingularity.lean` and checked their domain is C and that they require the missing continuity/boundedness condition. They do not prove unrestricted extension in C^m. Geometry searches return sphere compactness and `Orientation.kahler`; the latter is a bilinear form on a real plane, not a Kähler metric on projective space. The item searches return algebraic Proj and general sheaf/derived cohomology. None is an exact match or a one-line specialization. Both new nodes therefore remain unsplit, with no proof or proof dependencies.

## Not duplicates

lem-sfb-analytic-projective-kahler-geometry vs lem-sfb-smooth-analytification-cotangent: the latter constructs manifolds and cotangent identifications for smooth separated schemes; it does not give compactness, a Kähler metric, the displayed Fubini--Study form or the explicit punctured-affine quotient sections.

lem-sfb-analytic-projective-kahler-geometry vs lem-sfb-algebraic-dolbeault-derivative-comparison: the latter gives the GAGA/Dolbeault derivative comparison on smooth projective schemes and mentions their induced metric, but neither gives the quotient sections nor the chartwise metric construction; moreover using it here would form a cycle through GAGA. The new node isolates independent analytic projective geometry, not a second derivative-comparison theorem.

lem-sfb-analytic-projective-kahler-geometry vs lem-sfb-projective-harmonic-representatives: the latter gives harmonic representatives and their closedness, not a construction of compact projective geometry or its quotient sections. Its dependency path through GAGA prevents its use here.

lem-sfb-hartogs-punctured-affine-extension vs lem-sbc-depth-two-hartogs-restriction: the existing result concerns algebraic depth and module sections on punctured spectra. The new result extends arbitrary holomorphic functions on punctured complex affine space without an algebraic hypothesis. The same distinction applies to the other depth-two algebraic Hartogs nodes found by the DAG-wide search. No new node has a Stacks tag shared with an existing one: these are analytic inputs, not Stacks algebraic results.

## Review by N6

I checked Serre's original Lemma 4 at printed pp.20--21 online. Its setting has already reduced to projective space, its q=0 assertion is constants, and its q>0 argument is Dolbeault followed by the Kähler computation. The split supplies that computation and keeps cohomology in sheaves of C-vector spaces throughout. I read Demailly's Hartogs theorem (3.28), which allows removing a compact subset when the complement is connected; taking the origin in C^m is valid for m>=2. I read the quotient/charts paragraph V §15.A and the Fubini--Study example VI (4.4). The geometric statement spells out the sections given by normalization of a homogeneous coordinate and handles n=0 separately by its zero tangent bundle. Its positivity convention has g(v,w)=omega(v,Jw), hence omega(v,Jv)>0. No SGA source is used.

Step 1 uses the new geometric statement for all of compactness, Hausdorffness, second countability and the actual metric. I opened `lem-sc-ringed-space-module-sheaves-enough-injectives`: it applies to every ringed space, so the constant C sheaf qualifies. I opened `lem-sfb-dolbeault-acyclic-resolution`: it explicitly states exactness and global-sections acyclicity in C-vector-space sheaves, not just a local Poincaré lemma. I opened `lem-sfb-ringed-acyclic-resolution-derived-maps`: its statement supplies the derived acyclic-resolution comparison; the sites here are the set of opens in a containing universe, with the whole space terminal, both resolutions are nonnegative, and the identity map preserves augmentations. Its isomorphism is in D+(Ab), which is sufficient: a complex vector space is zero if its underlying group is zero. No unproved C-linearity of a comparison is required. The enough-injectives node is the declared generic off-unit tool.

Step 2 uses the geometric statement for the quotient projection, Hartogs with m=n+1>=2 for extension, and the analytic operations node for composition, inverses and continuity. Scalar invariance is an equality of functions on the punctured affine space. Letting a positive real scalar tend to zero proves the constant value, and evaluation at a specified projective point proves uniqueness.

Step 3 uses exactly the same Hartogs assertion coefficient by coefficient, and the analytic derivative/operations statements for the explicitly displayed differential of z_k/z_j. The coefficient calculation has scaling weight minus r: B_I(z)=t^r B_I(tz). I checked the sign of that weight; boundedness near zero follows from the entire extension, so r>0 forces zero. The geometric node really states the local sections s_j, and pulling back along them proves injectivity of pullback without assuming any unstated descent or comparison theorem.

Step 4 uses the exact orthogonal decomposition in `lem-sfb-hermitian-dolbeault-orthogonal-decomposition`, whose statement concerns actual smooth images, not their closures. Compactness and a Hermitian metric were established in step 1. The formal-adjoint identity stated there proves closedness of h and removes the coexact term by its displayed zero-norm calculation. Square-zero comes from the Dolbeault node. There is no application of a projective theorem which secretly depends on the item.

Step 5 uses `lem-sfb-kahler-laplacian-identity` for precisely Delta_d=2 Delta_barpartial, with the Kähler metric already in hand. The energy identity then proves dh=0. Conjugation commuting with real differentiation and separation of bidegrees are direct coordinate calculations. Exactness at A^{q,0} in the Dolbeault node identifies the closed conjugate as a holomorphic q-form; this is the exact clause used, and step 3 kills that form. Step 6 is elementary: alternating q-forms vanish above dimension, and the one-point space has exactly one coordinate chart with no differentials.

Small cases: n=0 has global sections C and no positive forms; n=1 uses Hartogs in C^2 (not the false C version), and the argument kills a potential holomorphic one-form before computing H^1(O). For q>n the resolution already has a zero term. For the new Hartogs statement, m=2 is the first permitted dimension, while m=1 is deliberately excluded since 1/z is a counterexample. For the new geometry statement, n=0 makes positivity vacuous, and at w=0 for n>0 the metric matrix is a positive multiple of the identity. The chart potential yields the positive matrix ((1+|w|^2)I - conjugate(w)w^T)/(1+|w|^2)^2, which is positive by Cauchy--Schwarz; overlapping potentials differ by log of the squared modulus of a nowhere-zero holomorphic coordinate ratio, whose mixed derivative is zero. These checks rule out a metric sign or gluing error.

I checked B--E against the written files. Every new node introduces all its objects, has statement only, has real logged searches and blueprint fields, and is smaller than the item. Every non-elementary step cites statements that actually contain its input. All six steps are below 2000 characters, and their arguments are explicit. I corrected the potential cycle by selecting the independent Hermitian/Kähler nodes before writing the proof. The statement and its statement dependencies are unchanged.

## Unfinished work

The two new inputs are intentionally statement-only stage-1 leaves awaiting their own splits. No part of this item's assembly proof is omitted. Required server checks and delivery follow this report.
