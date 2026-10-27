# path

A Lean implementation of lexical path cleaning, following the Go path.Clean rules. This is a Proven Commons project: it rebuilds a widely used rule in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet, and no plan issue has been posted. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

Clean a POSIX path string with the four rules of Go path.Clean.

## Main claim

Cleaning is idempotent. The result has no "." or empty element, and ".." only at the start. A cleaned relative path that does not start with ".." stays inside any folder it is joined to.

## Test oracles

- Go path.Clean and its tests.
- Python posixpath.normpath.
- Node path.posix.normalize.

The oracles differ on a leading "//", so the specification must choose a rule for that case and record it.

## Score

15 out of 18, from two scorers, in the round 3 sheet in the mission repo. The sheet is mission pull request 17.

## Placement note

The round 3 sheet raised the alternative of a module imported by the tar and zip projects, which each have their own path gate today. This repo was created at the org owner's direction, so the placement is a repo, not a module.

## What is not in this slice

- Filesystem access. This is string cleaning only.
- Windows path rules.
- Any claim about a full filesystem implementation.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
