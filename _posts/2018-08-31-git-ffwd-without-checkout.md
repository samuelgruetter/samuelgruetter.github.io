---
layout: post
title:  "Git: Fast-forwarding a branch without checking it out"
---

When using git, I sometimes want to fast-forward some `branchA`, but currently I'm on `branchB`. The simplest way to do this is to checkout `branchA`, do a pull (or another command to fast-forward `branchA`), and then to checkout `branchB` again.

However, when switching branches, git modifies my source files, so when I'm back on `branchB` and recompile, `make` will think many files changed, and the recompilation might take a long time.

So it would be nice to fast-forward branches without checking them out, and here's how to do it.

<!--more-->


### Fast-forwarding a local branch with new commits from a remote

Suppose I'm on a branch called `feature`, and I want to diff the work I'm doing on this branch against `master`, but my local `master` is not up to date.

I can update my `master` as follows:

```
git fetch origin master:master
```

More generally, this is the syntax of the command:

```
git fetch FROM_WHICH_REMOTE FROM_BRANCH:TO_BRANCH
```


### Fast-forwarding a local branch with new commits from another local branch

Suppose I'm still on my branch called `feature`, and I'm happy with the changes I did, and want them to be on `master`, without any merge commit.

Turns out I can also use `git fetch` for this, even though I don't want to perform any network operation:

```
git fetch . feature:master
```

The trick is that `.` denotes the "remote" which is my local clone.

The other direction sometimes also makes sense: Suppose I'm on `master`, and made something a bit experimental, did not commit it yet, and want to commit it to branch `featureX`. If there was no branch called `featureX` yet, I could just do `git checkout -b featureX`, but if it already exists (but has been merged into `master`), I first have to update it to current `master`. So I can "fetch my local `master` into `featureX`":

```
git fetch . master:featureX
```
