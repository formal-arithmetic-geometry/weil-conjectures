# Q17 basis-cone definition ownership (maintenance, 2026-10-24)

## Reason

The return of Q17/lem-trf-basis-cone-polynomial-normal at 5263e2f46f22
requires extracting basisCone, basisConeVariable and basisConeInclusion from
the localization theorem module into a definition-node-owned module. The
worker completed the extraction and all three files compiled, but the
stage-2 delivery reader excludes the localization node from the item's
prerequisite closure. Its advisory exclusion also drops module ownership,
so the otherwise valid repair fails with "no node of the delivery has it
as lean.file". Repeated dispatch cannot resolve this scope mismatch.

## Old

BasisConeGroupLocalization declared the three shared definitions alongside
its theorem; no definition node owned them. The polynomial-normal item
could cite only the unrelated localization theorem node for these notions.

## New

Maintenance installs the prepared extraction as a shared library repair.
The new def-trf-basis-cone-algebra owns BasisConeAlgebra and the three
existing declarations. BasisConeGroupLocalization publicly imports it and
its node cites the actual definition dependency in stmt_deps. The moved
signatures and bodies and the entire retained localization theorem,
including its proof-plan docstring, were compared byte for byte.

## Users

The localization module is the only existing Lean source declaring or
using these names. The prepared Q17 polynomial-normal module imports
BasisConeAlgebra directly and cites its definition node. Both consumers
and the definition module are checked separately with tools/lean_file.sh,
60 seconds per file, before the maintenance commit.

## Status

The shared extraction is installed by this commit. It does not deliver or
approve the polynomial-normal theorem. The worker's retained packet now
needs only its item node, BasisConePolynomialNormal.lean and report.md.
The four shared node/module copies have adjacent maintenance .bak backups
and are removed from the active sandbox packet after this commit.
Run batch2/deliver2.py Q17 lem-trf-basis-cone-polynomial-normal --no-push,
then deliver through the usual path for independent review. Do not restore
the localization theorem as an unused statement or proof dependency.

No launcher, preflight, review or landing tool is changed. The general
reader issue would be repaired by preserving module ownership independently
of the eligibility advisory, or by explicitly representing authorized
extraction repairs; those tools are outside this maintenance assignment.
